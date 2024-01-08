/* Lama SM Bytecode interpreter */

#include "../runtime/gc.h"
#include "../runtime/runtime.h"
#include "../runtime/runtime_common.h"

#include <errno.h>
#include <malloc.h>
#include <stdio.h>
#include <string.h>

void *__stop_custom_data  = 0;
void *__start_custom_data = 0;

/* The unpacked representation of bytecode file */
typedef struct {
  char *string_ptr; /* A pointer to the beginning of the string table */
  int  *public_ptr; /* A pointer to the beginning of publics table    */
  char *code_ptr; /* A pointer to the bytecode itself               */
  int  *global_ptr; /* A pointer to the global area                   */
  int   stringtab_size; /* The size (in bytes) of the string table        */
  int   global_area_size; /* The size (in words) of global area             */
  int   public_symbols_number; /* The number of public symbols                   */
  char  buffer[0];
} bytefile;

/* Gets a string from a string table by an index */
char *get_string (bytefile *f, int pos) { return &f->string_ptr[pos]; }

/* Gets a name for a public symbol */
char *get_public_name (bytefile *f, int i) { return get_string(f, f->public_ptr[i * 2]); }

/* Gets an offset for a publie symbol */
int get_public_offset (bytefile *f, int i) { return f->public_ptr[i * 2 + 1]; }

/* Reads a binary bytecode file by name and unpacks it */
bytefile *read_file (char *fname) {
  FILE     *f = fopen(fname, "rb");
  long      size;
  bytefile *file;

  if (f == 0) { failure("%s\n", strerror(errno)); }

  if (fseek(f, 0, SEEK_END) == -1) { failure("%s\n", strerror(errno)); }

  file = (bytefile *)malloc(sizeof(int) * 4 + (size = ftell(f)));

  if (file == 0) { failure("*** FAILURE: unable to allocate memory.\n"); }

  rewind(f);

  if (size != fread(&file->stringtab_size, 1, size, f)) { failure("%s\n", strerror(errno)); }

  fclose(f);

  file->string_ptr = &file->buffer[file->public_symbols_number * 2 * sizeof(int)];
  file->public_ptr = (int *)file->buffer;
  file->code_ptr   = &file->string_ptr[file->stringtab_size];
  file->global_ptr = (int *)malloc(file->global_area_size * sizeof(int));

  return file;
}

enum {
  HI_STOP  = 15,
  HI_BINOP = 0,
  HI_1,
  HI_LD,
  HI_LDA,
  HI_ST,
  HI_2,
  HI_PATT,
  HI_BUILTIN,
};

#define MACRO_BINOPS(E)                                                                            \
  E(ADD, +)                                                                                        \
  E(SUB, -)                                                                                        \
  E(MUL, *)                                                                                        \
  E(DIV, /)                                                                                        \
  E(MOD, %)                                                                                        \
  E(LT, <)                                                                                         \
  E(LE, <=)                                                                                        \
  E(GT, >)                                                                                         \
  E(GE, >=)                                                                                        \
  E(EQ, ==)                                                                                        \
  E(NE, !=)                                                                                        \
  E(AND, &&)                                                                                       \
  E(OR, ||)

enum {
  _BINOP_DUMMY = 0,

#define ENTRY(name, op) BINOP_##name,
  MACRO_BINOPS(ENTRY)
#undef ENTRY
};

enum {
  LO_1_CONST,
  LO_1_STRING,
  LO_1_SEXP,
  LO_1_STI,
  LO_1_STA,
  LO_1_JMP,
  LO_1_END,
  LO_1_RET,
  LO_1_DROP,
  LO_1_DUP,
  LO_1_SWAP,
  LO_1_ELEM,
};

enum {
  LO_2_CJMP_Z = 0,
  LO_2_CJMP_NZ,
  LO_2_BEGIN,
  LO_2_CBEGIN,
  LO_2_CLOSURE,
  LO_2_CALLC,
  LO_2_CALL,
  LO_2_TAG,
  LO_2_ARRAY,
  LO_2_FAIL,
  LO_2_LINE,
};

enum {
  BUILTIN_READ = 0,
  BUILTIN_WRITE,
  BUILTIN_LENGTH,
  BUILTIN_STRING,
  BUILTIN_ARRAY,
};

enum { MEM_G = 0, MEM_L, MEM_A, MEM_C };

enum {
  PATT_EQ_STRING = 0,
  PATT_TAG_STRING,
  PATT_TAG_ARRAY,
  PATT_TAG_SEXP,
  PATT_TAG_REF,
  PATT_TAG_VAL,
  PATT_TAG_FUN,
};

extern size_t __gc_stack_top, __gc_stack_bottom;

/* Т.к. сборщик мусора рассчитан на один стек,
   сделаем его глобальным */
#define STACK_SIZE (512 * 1024) /* 2 МБ стека, должно хватить на всё */
static size_t stack_data[STACK_SIZE];

/* Данные виртуальной машины будем хранить глобально,
   чтобы можно было легко писать вспомогательные функции,
   тем более что всё равно нужен глобальный стек */
static size_t *p_globals = 0;
static size_t *p_args    = 0;
static size_t *p_locals  = 0;
static size_t *p_closed  = 0;

static int nglobal    = 0;
static int fn_nlocals = 0;
static int fn_nargs   = 0;
static int fn_nclosed = 0;

static size_t *p_stack_frame = 0;

static char *p_instr = 0;

static inline size_t *s_top () { return (size_t *)__gc_stack_top + 1; }

static inline void s_push (size_t x) {
  if (__gc_stack_top < (size_t)stack_data) failure("Stack overflow\n");
  *(size_t *)__gc_stack_top = x;
  __gc_stack_top -= sizeof(size_t);
}

static inline size_t s_pop () {
  __gc_stack_top += sizeof(size_t);
  /* Глобальные переменные никогда не должны быть сняты со стека */
  if (__gc_stack_top >= (size_t)p_globals) failure("Stack underflow\n");
  size_t res = *(size_t *)__gc_stack_top;
  return res;
}

static inline size_t n_vars (int mem_type) {
  switch (mem_type) {
    case MEM_G: return nglobal;
    case MEM_L: return fn_nlocals;
    case MEM_A: return fn_nargs;
    case MEM_C: return fn_nclosed;
    default: /* Не может быть такого типа */ return 0;
  }
}

/* Barray, Bsexp и Bclosure не подходят, т.к. в них элементы передаются через varargs */
static size_t Warray (int n) {
  data *obj = alloc_array(n);
  int  *arr = (int *)obj->contents;
  for (int i = 0; i < n; ++i) {
    int x          = s_pop();
    arr[n - 1 - i] = x;
  }
  return (size_t)obj->contents;
}

static size_t Wsexp (char *tag, int n) {
  sexp *s   = alloc_sexp(n);
  data *obj = (data *)s;
  int  *arr = (int *)obj->contents;
  s->tag    = UNBOX(LtagHash(tag));
  for (int i = 0; i < n; ++i) {
    int x      = s_pop();
    arr[n - i] = x;
  }
  return (size_t)obj->contents;
}

static size_t Wclosure (int entry, int n) {
  data *obj = alloc_closure(n + 1);
  int  *arr = (int *)obj->contents;
  arr[0]    = entry;
  for (int i = 0; i < n; ++i) {
    size_t x   = s_pop();
    arr[n - i] = x;
  }
  return (size_t)obj->contents;
}

/* Структура стекового фрейма:
   - [Опционально] Объект замыкания
   - Аргументы функции
   - Адрес возврата в виде числа, ещё один бит сообщает о замыкании
   - Локальные переменные
   - Количество аргументов
   - Количество локальных переменных
   - Адрес предыдущего стекового фрейма

   Указатели на стек и на код будем записывать как числа,
   чтобы сборщик мусора не пытался их обрабатывать как объекты.

   Будем считать, что байткод корректен, допускаем неопределённое поведение,
   т.к. его же допускает исходная реализация Ламы.

   Будем добавлять 1 в младший бит указателей не на кучу Ламы,
   чтобы сборщик мусора считал их целыми числами. */

static inline void do_begin () {
  /* Адрес возврата, замыкание, аргументы */
  size_t *stack_top = s_top();
  p_args            = stack_top + fn_nargs;
  int ret_addr      = stack_top[0];
  if (ret_addr & 0x80000000) {
    /* Замыкание */
    size_t closure = p_args[1];
    data  *obj     = TO_DATA(closure);
    fn_nclosed     = LEN(obj->data_header) - 1;
    p_closed       = (size_t *)obj->contents + 1;
  } else {
    /* Обычная функция, без замыкания */
    fn_nclosed = 0;
    p_closed   = 0;
  }

  /* Выделим место для локальных переменных.
     Их обязательно нужно занулять,
     чтобы сборщик мусора не принимал
     неинициализированные переменные за указатели. */
  for (int i = 0; i < fn_nlocals; ++i) s_push(BOX(0));
  p_locals = s_top();

  s_push(BOX(fn_nargs));
  s_push(BOX(fn_nlocals));

  /* Где находится предыдущий стековый фрейм */
  s_push((size_t)p_stack_frame);
  p_stack_frame = s_top();
}

static void interpret (bytefile *bf) {
  __gc_init();
  __gc_stack_bottom = (size_t)(stack_data + STACK_SIZE);
  __gc_stack_top    = __gc_stack_bottom - sizeof(size_t);

  /* Будем хранить глобальные переменные также на стеке,
     чтобы их тоже видел сборщик мусора */
  for (int i = 0; i < bf->global_area_size; ++i) s_push(BOX(0));
  p_globals = s_top();
  nglobal   = bf->global_area_size;

  /* Фиктивный адрес возврата для главной функции */
  s_push(BOX(0));

#define INT (p_instr += sizeof(int), *(int *)(p_instr - sizeof(int)))
#define BYTE *p_instr++
#define STRING get_string(bf, INT)
#define FAIL failure("ERROR: invalid opcode %d-%d\n", h, l)
#define UNUSED failure("Unused instruction, line %d\n", __LINE__)

  p_instr = bf->code_ptr;

  for (;;) {
    char opcode = BYTE, h = (opcode & 0xF0) >> 4, l = opcode & 0x0F;

    switch (h) {
      case HI_STOP: goto stop;

      case HI_BINOP: {
        int y = UNBOX(s_pop());
        int x = UNBOX(s_pop());
        int z = 0;
        switch (l) {
#define ENTRY(name, op)                                                                            \
  case BINOP_##name: z = x op y; break;
          MACRO_BINOPS(ENTRY)
#undef ENTRY
        }
        s_push(BOX(z));
      } break;

      case HI_1:
        switch (l) {
          case LO_1_CONST: {
            int x = INT;
            s_push(BOX(x));
          } break;

          case LO_1_STRING: {
            char *cstr = STRING;
            void *str  = Bstring(cstr);
            s_push((size_t)str);
          } break;

          case LO_1_SEXP: {
            char  *tag    = STRING;
            int    nelems = INT;
            size_t x      = Wsexp(tag, nelems);
            s_push(x);
          } break;

          case LO_1_STI: UNUSED; break;

          case LO_1_STA: {
            size_t v = s_pop();
            size_t i = s_pop();
            /* Будем различать адреса переменных и индексы по старшему
               не знаковому биту индекса. Младший отнимается BOX'ом,
               поэтому получается, что настоящий адрес --- 29-битный */
            if (i & 0x40000000) {
              int pos         = i & ~0x40000000;
              pos             = UNBOX(pos);
              stack_data[pos] = v;
              s_push(v);
            } else {
              size_t x = s_pop();
              size_t y = (size_t)Bsta((void *)v, i, (void *)x);
              s_push(y);
            }
          } break;

          case LO_1_JMP: {
            int addr = INT;
            p_instr  = bf->code_ptr + addr;
          } break;

          case LO_1_END: {
            size_t  retval       = s_pop();
            size_t *p_prev_frame = (size_t *)*p_stack_frame;
            if (p_prev_frame == 0) {
              /* Выходим из главной функции */
              goto stop;
            }
            int frame_size = fn_nlocals + fn_nargs + 4;
            int ret_addr   = p_stack_frame[3 + fn_nlocals];
            if (ret_addr & 0x80000000) {
              /* Возврат из замыкания */
              ++frame_size;
              ret_addr &= 0x7FFFFFFF;
            }
            p_instr = bf->code_ptr + ret_addr;

            /* Убираем текущий фрейм */
            for (int i = 0; i < frame_size; ++i) s_pop();
            p_stack_frame = p_prev_frame;

            fn_nlocals = UNBOX(p_stack_frame[1]);
            fn_nargs   = UNBOX(p_stack_frame[2]);

            p_locals = p_stack_frame + 3;
            /* Можно переставлять местами аргументы при вызове,
               т.к. на вершине стека перед вызовом --- последний,
               но проще поменять знак при разыменовании */
            p_args = p_locals + fn_nlocals + fn_nargs;

            ret_addr = p_stack_frame[3 + fn_nlocals];
            if (ret_addr & 0x80000000) {
              /* Вернулись в замыкание */
              size_t closure = p_args[1];
              data  *obj     = TO_DATA(closure);
              fn_nclosed     = LEN(obj->data_header) - 1;
              p_closed       = (size_t *)obj->contents + 1;
            } else {
              /* Вернулись в обычную функцию */
              fn_nclosed = 0;
              p_closed   = 0;
            }
            s_push(retval);
          } break;

          case LO_1_RET: UNUSED; break;

          case LO_1_DROP: s_pop(); break;

          case LO_1_DUP: {
            size_t x = *(size_t *)s_top();
            s_push(x);
          } break;

          case LO_1_SWAP: UNUSED; break;

          case LO_1_ELEM: {
            size_t i = s_pop();
            size_t p = s_pop();
            size_t y = (size_t)Belem((void *)p, i);
            s_push(y);
          } break;

          default: FAIL;
        }
        break;

      case HI_LD: {
        int i = INT;

        size_t n = n_vars(l);
        if (i < 0 || i >= n)
          failure("Addressing %dth variable of type %d when only %d exist\n", i, l, n);

        size_t x = 0;
        switch (l) {
          case MEM_G: x = p_globals[i]; break;
          case MEM_L: x = p_locals[i]; break;
          case MEM_A: x = p_args[-i]; break;
          case MEM_C: x = p_closed[i]; break;
          default: FAIL;
        }
        s_push(x);
      } break;

      case HI_LDA: {
        size_t *addr = 0;
        int     i    = INT;

        size_t n = n_vars(l);
        if (i < 0 || i >= n)
          failure("Addressing %dth variable of type %d when only %d exist\n", i, l, n);

        switch (l) {
          case MEM_G: addr = p_globals + i; break;
          case MEM_L: addr = p_locals + i; break;
          case MEM_A: addr = p_args - i; break;
          case MEM_C: addr = p_closed + i; break;
          default: FAIL;
        }
        size_t pos = addr - stack_data;
        s_push(BOX(pos) | 0x40000000);
      } break;

      case HI_ST: {
        int i = INT;

        size_t n = n_vars(l);
        if (i < 0 || i >= n)
          failure("Addressing %dth variable of type %d when only %d exist\n", i, l, n);

        size_t x = *(size_t *)s_top();
        switch (l) {
          case MEM_G: p_globals[i] = x; break;
          case MEM_L: p_locals[i] = x; break;
          case MEM_A: p_args[-i] = x; break;
          case MEM_C: p_closed[i] = x; break;
          default: FAIL;
        }
      } break;

      case HI_2:
        switch (l) {
          case LO_2_CJMP_Z: {
            int    addr = INT;
            size_t x    = s_pop();
            if (UNBOX(x) == 0) p_instr = bf->code_ptr + addr;
          } break;

          case LO_2_CJMP_NZ: {
            int    addr = INT;
            size_t x    = s_pop();
            if (UNBOX(x) != 0) p_instr = bf->code_ptr + addr;
          } break;

          case LO_2_BEGIN:
            fn_nargs   = INT;
            fn_nlocals = INT;
            do_begin();
            break;

          case LO_2_CBEGIN:
            fn_nargs   = INT;
            fn_nlocals = INT;
            /* Т.к. замыкание может быть ссылкой на функцию,
               то его наличие на стеке придётся проверять и
               в обычном BEGIN */
            do_begin();
            break;

          case LO_2_CLOSURE: {
            int entry = INT;
            int n     = INT;
            for (int j = 0; j < n; j++) {
              char pos_type = BYTE;
              int  i        = INT;

              size_t n = n_vars(pos_type);
              if (i < 0 || i >= n)
                failure("Addressing %dth variable of type %d when only %d exist\n", i, l, n);

              size_t x = 0;
              switch (pos_type) {
                case MEM_G: x = p_globals[i]; break;
                case MEM_L: x = p_locals[i]; break;
                case MEM_A: x = p_args[-i]; break;
                case MEM_C: x = p_closed[i]; break;
                default: FAIL;
              }
              s_push(x);
            }
            size_t closure = Wclosure(entry, n);
            s_push(closure);
          } break;

          case LO_2_CALLC: {
            int nargs = INT;
            /* Снять замыкание со стека, если у него нет аргументов, здесь нельзя.
               Придётся обрабатывать наличие замыкания в BEGIN */
            size_t closure  = s_top()[nargs];
            data  *obj      = TO_DATA(closure);
            int   *arr      = (int *)obj->contents;
            int    addr     = arr[0];
            size_t ret_addr = (p_instr - bf->code_ptr) | 0x80000000;
            s_push(ret_addr);
            p_instr = bf->code_ptr + addr;
          } break;

          case LO_2_CALL: {
            int    addr     = INT;
            int    nargs    = INT;
            size_t ret_addr = p_instr - bf->code_ptr;
            s_push(ret_addr);
            p_instr = bf->code_ptr + addr;
          } break;

          case LO_2_TAG: {
            char  *tag    = STRING;
            int    nelems = INT;
            size_t x      = s_pop();
            int    hash   = LtagHash(tag);
            int    y      = Btag((void *)x, hash, BOX(nelems));
            s_push(y);
          } break;

          case LO_2_ARRAY: {
            int    n = INT;
            size_t x = s_pop();
            size_t y = Barray_patt((void *)x, BOX(n));
            s_push(y);
          } break;

          case LO_2_FAIL: {
            int line = INT;
            int col  = INT;
            failure("%d:%d\n", line, col);
          } break;

          case LO_2_LINE: {
            /* Игнорируем эту инструкцию,
               также как и в исходной реализации Ламы */
            (void)INT;
          } break;

          default: FAIL;
        }
        break;

      case HI_PATT:
        switch (l) {
          case PATT_EQ_STRING: {
            size_t y = s_pop();
            size_t x = s_pop();
            size_t z = Bstring_patt((void *)x, (void *)y);
            s_push(z);
          } break;
          case PATT_TAG_STRING: {
            size_t x = s_pop();
            size_t y = Bstring_tag_patt((void *)x);
            s_push(y);
          } break;
          case PATT_TAG_ARRAY: {
            size_t x = s_pop();
            size_t y = Barray_tag_patt((void *)x);
            s_push(y);
          } break;
          case PATT_TAG_SEXP: {
            size_t x = s_pop();
            size_t y = Bsexp_tag_patt((void *)x);
            s_push(y);
          } break;
          case PATT_TAG_REF: {
            size_t x = s_pop();
            size_t y = Bboxed_patt((void *)x);
            s_push(y);
          } break;
          case PATT_TAG_VAL: {
            size_t x = s_pop();
            size_t y = Bunboxed_patt((void *)x);
            s_push(y);
          } break;
          case PATT_TAG_FUN: {
            size_t x = s_pop();
            size_t y = Bclosure_tag_patt((void *)x);
            s_push(y);
          } break;
          default: FAIL; break;
        }
        break;

      case HI_BUILTIN: {
        switch (l) {
          case BUILTIN_READ: {
            int x = Lread();
            s_push(x);
          } break;

          case BUILTIN_WRITE: {
            size_t x = s_pop();
            size_t y = Lwrite(x);
            s_push(y);
          } break;

          case BUILTIN_LENGTH: {
            size_t x = s_pop();
            size_t y = Llength((void *)x);
            s_push(y);
          } break;

          case BUILTIN_STRING: {
            size_t x = s_pop();
            size_t y = (size_t)Lstring((void *)x);
            s_push(y);
          } break;

          case BUILTIN_ARRAY: {
            int    n = INT;
            size_t x = Warray(n);
            s_push(x);
          } break;

          default: FAIL;
        }
      } break;

      default: FAIL;
    }
  }

stop:
  __shutdown();
}

int main (int argc, char *argv[]) {
  bytefile *f = read_file(argv[1]);
  interpret(f);
  free(f->global_ptr);
  free(f);
  return 0;
}

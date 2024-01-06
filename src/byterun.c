/* Lama SM Bytecode interpreter */

#include "../runtime/gc.h"
#include "../runtime/runtime.h"
#include "../runtime/runtime_common.h"
#include "../runtime/virt_stack.h"
#include <alloca.h>
#include <errno.h>
#include <malloc.h>
#include <stdio.h>
#include <string.h>

void *__start_custom_data;
void *__stop_custom_data;

/* The unpacked representation of bytecode file */
typedef struct {
  char *string_ptr;            /* A pointer to the beginning of the string table */
  int  *public_ptr;            /* A pointer to the beginning of publics table    */
  char *code_ptr;              /* A pointer to the bytecode itself               */
  int  *global_ptr;            /* A pointer to the global area                   */
  int   stringtab_size;        /* The size (in bytes) of the string table        */
  int   global_area_size;      /* The size (in words) of global area             */
  int   public_symbols_number; /* The number of public symbols                   */
  char  buffer[0];
} bytefile;

/* Gets a string from a string table by an index */
char *get_string(bytefile *f, int pos) { return &f->string_ptr[pos]; }

/* Gets a name for a public symbol */
char *get_public_name(bytefile *f, int i) { return get_string(f, f->public_ptr[i * 2]); }

/* Gets an offset for a publie symbol */
int get_public_offset(bytefile *f, int i) { return f->public_ptr[i * 2 + 1]; }

/* Reads a binary bytecode file by name and unpacks it */
bytefile *read_file(char *fname) {
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

/* Вспомогательные функции, чтобы стек правильно обрабатывался сборщиком мусора */
extern size_t __gc_stack_top, __gc_stack_bottom;

void s_push(virt_stack *st, size_t x) {
  vstack_push(st, x);
  __gc_stack_top = (size_t)((size_t *)vstack_top(st) - 1);
}

size_t s_pop(virt_stack *st) {
  size_t res     = vstack_pop(st);
  __gc_stack_top = (size_t)((size_t *)vstack_top(st) - 1);
  return res;
}

/* Не нужно переставлять указатели */
void s_swap(virt_stack *st) {
  if (vstack_size(st) < 2) failure("Stack underflow");
  size_t *top = vstack_top(st);
  size_t  x   = top[0];
  top[0]      = top[1];
  top[1]      = x;
}

/* runtime.h и runtime_common.h не экспортируют эти функции */
extern void *Bstring(void *);
extern void *Belem(void *p, int i);
extern void *Bsta(void *v, int i, void *x);
extern int   Lread();
extern int   Lwrite(int n);
extern int   Llength(void *p);
extern void *Lstring(void *);
extern int   LtagHash(char *s);
extern int   Btag(void *d, int t, int n);

/* Barray и Bsexp не подходят, т.к. в них элементы передаются через varargs */
size_t Warray(virt_stack *st, int n) {
  data *obj = alloc_array(n);
  int  *arr = (int *)obj->contents;
  for (int i = 0; i < n; ++i) {
    int x          = s_pop(st);
    arr[n - 1 - i] = x;
  }
  return (size_t)obj->contents;
}

size_t Wsexp(virt_stack *st, char *tag, int n) {
  sexp *s   = alloc_sexp(n);
  data *obj = (data *)s;
  int  *arr = (int *)obj->contents;
  s->tag    = LtagHash(tag);
  for (int i = 0; i < n; ++i) {
    int x      = s_pop(st);
    arr[n - i] = x;
  }
  return (size_t)obj->contents;
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

enum {
  BINOP_ADD = 1,
  BINOP_SUB,
  BINOP_MUL,
  BINOP_DIV,
  BINOP_MOD,
  BINOP_LT,
  BINOP_LE,
  BINOP_GT,
  BINOP_GE,
  BINOP_EQ,
  BINOP_NE,
  BINOP_AND,
  BINOP_OR,
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

/* Структура стекового фрейма:
   - Аргументы функции
   - Адрес возврата
   - Локальные переменные
   - Количество аргументов
   - Количество локальных переменных
   - Адрес предыдущего стекового фрейма

   Указатели на стек и на код будем записывать как числа,
   чтобы сборщик мусора не пытался их обрабатывать как объекты.

   Будем считать, что байткод корректен, допускаем неопределённое поведение,
   т.к. его же допускает исходная реализация Ламы */

void interpret(FILE *f, bytefile *bf) {
  __gc_init();
  /* Из runtime.c следует, что чтобы сборщик мусора работал корректно,
     стек виртуальной машины должен располагаться на стеке процесса */
  virt_stack *vstack = alloca(sizeof(virt_stack));
  if (!vstack) failure("Could not allocate vstack");
  vstack_init(vstack);
  __gc_stack_bottom = (size_t)vstack_top(vstack);
  __gc_stack_top    = __gc_stack_bottom;

  /* Будем хранить глобальные переменные также на стеке,
     чтобы их тоже видел сборщик мусора */
  for (int i = 0; i < bf->global_area_size; ++i) s_push(vstack, BOX(0));
  size_t *p_globals = vstack_top(vstack);

  int     stack_frame_pos = 0;
  int     stack_nargs     = 0;
  int     stack_nlocals   = 0;
  size_t *p_args          = 0;
  size_t *p_locals        = 0;

#define INT (ip += sizeof(int), *(int *)(ip - sizeof(int)))
#define BYTE *ip++
#define STRING get_string(bf, INT)
#define FAIL failure("ERROR: invalid opcode %d-%d\n", h, l)
#define TODO failure("Unimplemented, line %d\n", __LINE__)

  char *ip     = bf->code_ptr;
  char *ops[]  = {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
  char *pats[] = {"=str", "#string", "#array", "#sexp", "#ref", "#val", "#fun"};
  char *lds[]  = {"LD", "LDA", "ST"};
  do {
    char opcode = BYTE, h = (opcode & 0xF0) >> 4, l = opcode & 0x0F;
    fprintf(f, "0x%.8lx:\t", ip - bf->code_ptr - 1);

    switch (h) {
    case HI_STOP: goto stop;

    case HI_BINOP: {
      fprintf(f, "BINOP\t%s", ops[l - 1]);
      int y = UNBOX(s_pop(vstack));
      int x = UNBOX(s_pop(vstack));
      int z = 0;
      switch (l) {
      case BINOP_ADD: z = x + y; break;
      case BINOP_SUB: z = x - y; break;
      case BINOP_MUL: z = x * y; break;
      case BINOP_DIV: z = x / y; break;
      case BINOP_MOD: z = x % y; break;
      case BINOP_LT: z = x < y ? 1 : 0; break;
      case BINOP_LE: z = x <= y ? 1 : 0; break;
      case BINOP_GT: z = x > y ? 1 : 0; break;
      case BINOP_GE: z = x >= y ? 1 : 0; break;
      case BINOP_EQ: z = x == y ? 1 : 0; break;
      case BINOP_NE: z = x != y ? 1 : 0; break;
      case BINOP_AND: z = x && y ? 1 : 0; break;
      case BINOP_OR: z = x || y ? 1 : 0; break;
      }
      s_push(vstack, BOX(z));
    } break;

    case HI_1:
      switch (l) {
      case LO_1_CONST: {
        int x = INT;
        fprintf(f, "CONST\t%d", x);
        s_push(vstack, BOX(x));
      } break;

      case LO_1_STRING: {
        char *cstr = STRING;
        fprintf(f, "STRING\t%s", cstr);
        void *str = Bstring(cstr);
        s_push(vstack, (size_t)str);
      } break;

      case LO_1_SEXP: {
        char *tag    = STRING;
        int   nelems = INT;
        fprintf(f, "SEXP\t%s %d", tag, nelems);
        size_t x = Wsexp(vstack, tag, nelems);
        s_push(vstack, x);
      } break;

      case LO_1_STI:
        fprintf(f, "STI");
        TODO;
        break;

      case LO_1_STA: {
        fprintf(f, "STA");
        size_t v = s_pop(vstack);
        size_t i = s_pop(vstack);
        size_t x = s_pop(vstack);
        size_t y = (size_t)Bsta((void *)v, i, (void *)x);
        s_push(vstack, y);
      } break;

      case LO_1_JMP: {
        int addr = INT;
        fprintf(f, "JMP\t0x%.8x", addr);
        ip = bf->code_ptr + addr;
      } break;

      case LO_1_END: {
        fprintf(f, "END");

        int prev_frame_pos = UNBOX(vstack->buf[stack_frame_pos]);
        if (prev_frame_pos == 0) {
          /* Выходим из главной функции */
          goto stop;
        }
        int frame_size = stack_nlocals + stack_nargs + 4;
        int ret_addr   = UNBOX(vstack->buf[stack_frame_pos + 3 + stack_nlocals]);
        ip             = bf->code_ptr + ret_addr;

        /* Убираем текущий фрейм */
        for (int i = 0; i < frame_size; ++i) s_pop(vstack);
        stack_frame_pos = prev_frame_pos;

        stack_nlocals = UNBOX(vstack->buf[stack_frame_pos + 1]);
        stack_nargs   = UNBOX(vstack->buf[stack_frame_pos + 2]);

        p_locals = vstack->buf + stack_frame_pos + 3;
        p_args   = p_locals + stack_nlocals + 1;
      } break;

      case LO_1_RET:
        fprintf(f, "RET");
        TODO;
        break;

      case LO_1_DROP:
        fprintf(f, "DROP");
        s_pop(vstack);
        break;

      case LO_1_DUP: {
        fprintf(f, "DUP");
        size_t x = *(size_t *)vstack_top(vstack);
        s_push(vstack, x);
      } break;

      case LO_1_SWAP:
        fprintf(f, "SWAP");
        TODO;
        break;

      case LO_1_ELEM: {
        fprintf(f, "ELEM");
        size_t i = s_pop(vstack);
        size_t p = s_pop(vstack);
        size_t y = (size_t)Belem((void *)p, i);
        s_push(vstack, y);
      } break;

      default: FAIL;
      }
      break;

    case HI_LD: {
      fprintf(f, "%s\t", lds[h - 2]);
      int pos = INT;
      switch (l) {
      case MEM_G: {
        fprintf(f, "G(%d)", pos);
        size_t x = p_globals[pos];
        s_push(vstack, x);
      } break;
      case MEM_L: {
        fprintf(f, "L(%d)", pos);
        size_t x = p_locals[pos];
        s_push(vstack, x);
      } break;
      case MEM_A: {
        fprintf(f, "A(%d)", pos);
        size_t x = p_args[pos];
        s_push(vstack, x);
      } break;
      case MEM_C:
        fprintf(f, "C(%d)", pos);
        TODO;
        break;
      default: FAIL;
      }
    } break;

    case HI_LDA:
      fprintf(f, "%s\t", lds[h - 2]);
      switch (l) {
      case MEM_G:
        fprintf(f, "G(%d)", INT);
        TODO;
        break;
      case MEM_L:
        fprintf(f, "L(%d)", INT);
        TODO;
        break;
      case MEM_A:
        fprintf(f, "A(%d)", INT);
        TODO;
        break;
      case MEM_C:
        fprintf(f, "C(%d)", INT);
        TODO;
        break;
      default: FAIL;
      }
      break;

    case HI_ST: {
      int    pos = INT;
      size_t x   = *(size_t *)vstack_top(vstack);

      fprintf(f, "%s\t", lds[h - 2]);
      switch (l) {
      case MEM_G:
        fprintf(f, "G(%d)", pos);
        p_globals[pos] = x;
        break;
      case MEM_L:
        fprintf(f, "L(%d)", pos);
        p_locals[pos] = x;
        break;
      case MEM_A:
        fprintf(f, "A(%d)", pos);
        TODO;
        break;
      case MEM_C:
        fprintf(f, "C(%d)", pos);
        TODO;
        break;
      default: FAIL;
      }
    } break;

    case HI_2:
      switch (l) {
      case LO_2_CJMP_Z: {
        int addr = INT;
        fprintf(f, "CJMPz\t0x%.8x", addr);
        size_t x = s_pop(vstack);
        if (UNBOX(x) == 0) ip = bf->code_ptr + addr;
      } break;

      case LO_2_CJMP_NZ: {
        int addr = INT;
        fprintf(f, "CJMPnz\t0x%.8x", addr);
        size_t x = s_pop(vstack);
        if (UNBOX(x) != 0) ip = bf->code_ptr + addr;
      } break;

      case LO_2_BEGIN:
        stack_nargs   = INT;
        stack_nlocals = INT;
        fprintf(f, "BEGIN\t%d %d", stack_nargs, stack_nlocals);

        /* Аргументы и адрес возврата */
        p_args = (size_t *)vstack_top(vstack) + 1;

        /* Выделим место для локальных переменных */
        for (int i = 0; i < stack_nlocals; ++i) s_push(vstack, BOX(0));
        p_locals = vstack_top(vstack);

        s_push(vstack, BOX(stack_nargs));
        s_push(vstack, BOX(stack_nlocals));

        /* Где находится предыдущий стековый фрейм */
        s_push(vstack, BOX(stack_frame_pos));
        stack_frame_pos = vstack->cur;
        break;

      case LO_2_CBEGIN:
        fprintf(f, "CBEGIN\t%d ", INT);
        fprintf(f, "%d", INT);
        TODO;
        break;

      case LO_2_CLOSURE:
        fprintf(f, "CLOSURE\t0x%.8x", INT);
        {
          int n = INT;
          for (int i = 0; i < n; i++) {
            switch (BYTE) {
            case MEM_G: fprintf(f, "G(%d)", INT); break;
            case MEM_L: fprintf(f, "L(%d)", INT); break;
            case MEM_A: fprintf(f, "A(%d)", INT); break;
            case MEM_C: fprintf(f, "C(%d)", INT); break;
            default: FAIL;
            }
          }
        };
        TODO;
        break;

      case LO_2_CALLC:
        fprintf(f, "CALLC\t%d", INT);
        TODO;
        break;

      case LO_2_CALL: {
        int addr  = INT;
        int nargs = INT;
        fprintf(f, "CALL\t0x%.8x ", addr);
        fprintf(f, "%d", nargs);
        int ret_addr = ip - bf->code_ptr;
        s_push(vstack, BOX(ret_addr));
        ip = bf->code_ptr + addr;
      } break;

      case LO_2_TAG: {
        char *tag    = STRING;
        int   nelems = INT;
        fprintf(f, "TAG\t%s %d", tag, nelems);

        size_t x    = s_pop(vstack);
        int    hash = LtagHash(tag);
        int    y    = Btag((void *)x, BOX(hash), BOX(nelems));
        s_push(vstack, y);
      } break;

      case LO_2_ARRAY:
        fprintf(f, "ARRAY\t%d", INT);
        TODO;
        break;

      case LO_2_FAIL: {
        int line = INT;
        int col  = INT;
        fprintf(f, "FAIL\t%d %d", line, col);
        failure("%d:%d\n", line, col);
        TODO;
      } break;

      case LO_2_LINE: {
        /* LINE INT
           Игнорируем эту инструкцию, также как и в исходной реализации Ламы */
        int arg = INT;
        fprintf(f, "LINE\t%d", arg);
      } break;

      default: FAIL;
      }
      break;

    case HI_PATT:
      fprintf(f, "PATT\t%s", pats[l]);
      TODO;
      break;

    case HI_BUILTIN: {
      switch (l) {
      case BUILTIN_READ: {
        fprintf(f, "CALL\tLread");
        int x = Lread();
        s_push(vstack, x);
      } break;

      case BUILTIN_WRITE: {
        fprintf(f, "CALL\tLwrite");
        size_t x = s_pop(vstack);
        size_t y = Lwrite(x);
        s_push(vstack, y);
      } break;

      case BUILTIN_LENGTH: {
        fprintf(f, "CALL\tLlength");
        size_t x = s_pop(vstack);
        size_t y = Llength((void *)x);
        s_push(vstack, y);
      } break;

      case BUILTIN_STRING:
        fprintf(f, "CALL\tLstring");
        TODO;
        break;

      case BUILTIN_ARRAY: {
        int n = INT;
        fprintf(f, "CALL\tBarray\t%d", n);
        size_t x = Warray(vstack, n);
        s_push(vstack, x);
      } break;

      default: FAIL;
      }
    } break;

    default: FAIL;
    }

    fprintf(f, "\n");
  } while (1);

stop:
  fprintf(f, "<end>\n");
  __shutdown();
}

int main(int argc, char *argv[]) {
  bytefile *f = read_file(argv[1]);
  interpret(stderr, f);
  free(f->global_ptr);
  free(f);
  return 0;
}

/* Lama SM Bytecode interpreter */

#include "../runtime/gc.h"
#include "../runtime/runtime.h"
#include "../runtime/runtime_common.h"
#include "../runtime/virt_stack.h"
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

// runtime.h и runtime_common.h не экспортируют Bstring
extern void *Bstring(void *);
// Barray и Bsexp не подходят, т.к. в них элементы передаются через varargs

// Вспомогательные функции,
// чтобы стек правильно обрабатывался
// сборщиком мусора
extern size_t __gc_stack_top, __gc_stack_bottom;

void s_push(virt_stack *st, size_t x) {
  vstack_push(st, x);
  __gc_stack_top = (size_t)&st->buf[st->cur];
}

size_t s_pop(virt_stack *st) {
  size_t res     = vstack_pop(st);
  __gc_stack_top = (size_t)&st->buf[st->cur];
  return res;
}

void interpret(FILE *f, bytefile *bf) {
  virt_stack *vstack = vstack_create();
  if (!vstack) failure("Could not allocate vstack");
  vstack_init(vstack);
  __gc_stack_top = (size_t)&vstack->buf[vstack->cur];
  __gc_stack_top = (size_t)&vstack->buf[vstack->cur];

#define INT (ip += sizeof(int), *(int *)(ip - sizeof(int)))
#define BYTE *ip++
#define STRING get_string(bf, INT)
#define FAIL failure("ERROR: invalid opcode %d-%d\n", h, l)
#define TODO failure("Unimplemented, line %d\n", __LINE__);

  char *ip     = bf->code_ptr;
  char *ops[]  = {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
  char *pats[] = {"=str", "#string", "#array", "#sexp", "#ref", "#val", "#fun"};
  char *lds[]  = {"LD", "LDA", "ST"};
  do {
    char x = BYTE, h = (x & 0xF0) >> 4, l = x & 0x0F;

    fprintf(f, "0x%.8lx:\t", ip - bf->code_ptr - 1);

    switch (h) {
    case 15: TODO goto stop;

    /* BINOP */
    case 0: TODO fprintf(f, "BINOP\t%s", ops[l - 1]); break;

    case 1:
      switch (l) {
      case 0: TODO fprintf(f, "CONST\t%d", INT); break;

      case 1: TODO fprintf(f, "STRING\t%s", STRING); break;

      case 2:
        TODO fprintf(f, "SEXP\t%s ", STRING);
        fprintf(f, "%d", INT);
        break;

      case 3: TODO fprintf(f, "STI"); break;

      case 4: TODO fprintf(f, "STA"); break;

      case 5: TODO fprintf(f, "JMP\t0x%.8x", INT); break;

      case 6: TODO fprintf(f, "END"); break;

      case 7: TODO fprintf(f, "RET"); break;

      case 8: TODO fprintf(f, "DROP"); break;

      case 9: TODO fprintf(f, "DUP"); break;

      case 10: TODO fprintf(f, "SWAP"); break;

      case 11: TODO fprintf(f, "ELEM"); break;

      default: FAIL;
      }
      break;

    case 2:
    case 3:
    case 4:
      fprintf(f, "%s\t", lds[h - 2]);
      switch (l) {
      case 0: TODO fprintf(f, "G(%d)", INT); break;
      case 1: TODO fprintf(f, "L(%d)", INT); break;
      case 2: TODO fprintf(f, "A(%d)", INT); break;
      case 3: TODO fprintf(f, "C(%d)", INT); break;
      default: FAIL;
      }
      break;

    case 5:
      switch (l) {
      case 0: TODO fprintf(f, "CJMPz\t0x%.8x", INT); break;

      case 1: TODO fprintf(f, "CJMPnz\t0x%.8x", INT); break;

      case 2:
        TODO fprintf(f, "BEGIN\t%d ", INT);
        fprintf(f, "%d", INT);
        break;

      case 3:
        TODO fprintf(f, "CBEGIN\t%d ", INT);
        fprintf(f, "%d", INT);
        break;

      case 4:
        TODO fprintf(f, "CLOSURE\t0x%.8x", INT);
        {
          int n = INT;
          for (int i = 0; i < n; i++) {
            switch (BYTE) {
            case 0: fprintf(f, "G(%d)", INT); break;
            case 1: fprintf(f, "L(%d)", INT); break;
            case 2: fprintf(f, "A(%d)", INT); break;
            case 3: fprintf(f, "C(%d)", INT); break;
            default: FAIL;
            }
          }
        };
        break;

      case 5: TODO fprintf(f, "CALLC\t%d", INT); break;

      case 6:
        TODO fprintf(f, "CALL\t0x%.8x ", INT);
        fprintf(f, "%d", INT);
        break;

      case 7:
        TODO fprintf(f, "TAG\t%s ", STRING);
        fprintf(f, "%d", INT);
        break;

      case 8: TODO fprintf(f, "ARRAY\t%d", INT); break;

      case 9:
        TODO fprintf(f, "FAIL\t%d", INT);
        fprintf(f, "%d", INT);
        break;

      case 10: TODO fprintf(f, "LINE\t%d", INT); break;

      default: FAIL;
      }
      break;

    case 6: TODO fprintf(f, "PATT\t%s", pats[l]); break;

    case 7: {
      switch (l) {
      case 0: TODO fprintf(f, "CALL\tLread"); break;

      case 1: TODO fprintf(f, "CALL\tLwrite"); break;

      case 2: TODO fprintf(f, "CALL\tLlength"); break;

      case 3: TODO fprintf(f, "CALL\tLstring"); break;

      case 4: TODO fprintf(f, "CALL\tBarray\t%d", INT); break;

      default: FAIL;
      }
    } break;

    default: FAIL;
    }

    fprintf(f, "\n");
  } while (1);
stop:
  fprintf(f, "<end>\n");
}

int main(int argc, char *argv[]) {
  bytefile *f = read_file(argv[1]);
  interpret(stdout, f);
  return 0;
}

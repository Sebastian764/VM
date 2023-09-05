/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2023                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t  S;   /* Operand stack of C0 values */
  ubyte       *P;   /* Function body */
  size_t       pc;  /* Program counter */
  c0_value    *V;   /* The local variables */
};

void push_int(c0v_stack_t S, int32_t i) 
{
  c0v_push(S, int2val(i));
}

int32_t pop_int(c0v_stack_t S)
{
  return val2int(c0v_pop(S));
}

void *pop_ptr(c0v_stack_t S)
{
  return val2ptr(c0v_pop(S));
}

void push_ptr(c0v_stack_t S, void *x) {
  c0v_push(S, ptr2val(x));
}

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  /* Variables */
  c0v_stack_t S = c0v_stack_new(); /* Operand stack of C0 values */
  ubyte *P = bc0->function_pool[0].code;      /* Array of bytes that make up the current function */
  size_t pc = 0;     /* Current location within the current byte array P */
  c0_value *V = xcalloc(bc0->function_pool[0].num_vars, sizeof(struct c0_value_header));
  // xcalloc(1, sizeof(struct c0_value_header));   /* Local variables (you won't need this till Task 2) */
  (void) V;      // silences compilation errors about V being currently unused

  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack = stack_new();
  (void) callStack; // silences compilation errors about callStack being currently unused

  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
            P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: { // // ----------------------------------------------------------
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP: {
      pc++;
      c0_value v1 = c0v_pop(S);
      c0_value v2 = c0v_pop(S);
      c0v_push(S,v1);
      c0v_push(S,v2);
      break;
    }


    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */

    case RETURN: {
      c0_value retval = c0v_pop(S);
      // ASSERT(c0v_stack_empty(S));
      c0_value *vCopy = V;
      c0v_stack_t sCopy = S;
      if (!stack_empty(callStack)) {
        frame* a = (frame*)pop(callStack); 
        ASSERT(c0v_stack_empty(S));
        S = a->S;
        P = a->P;
        V = a->V;
        pc = a->pc;

        free(a);
        free(vCopy);
        
        c0v_stack_free(sCopy);
        // stack_free(callStack, NULL);
        c0v_push(S, retval);
      // assert(!c0v_stack_empty(S));
        break;
      }
      free(vCopy);
      c0v_stack_free(sCopy);

      stack_free(callStack, NULL);
      // ASSERT(c0v_stack_empty(S));
// Another way to print only in DEBUG mode
// IF_DEBUG(fprintf(stderr, "Returning %d from execute()\n", retval));
      // Free everything before returning from the execute function!
      return val2int(retval);
    }                 


    /* Arithmetic and Logical operations */

    case IADD: {
      pc++;
      int32_t a = (int32_t)pop_int(S);
      int32_t b = (int32_t)pop_int(S);
      push_int(S, (a+b));
      break;
    }

    case ISUB: {
      pc++;
      int32_t a = (int32_t)pop_int(S);
      int32_t b = (int32_t)pop_int(S);
      push_int(S, (b-a));
      break;
    }
    case IMUL: {
      pc++;
      int32_t a = (int32_t)pop_int(S);
      int32_t b = (int32_t)pop_int(S);
      push_int(S, (a*b));
      break;
    }

    case IDIV: { 
      pc++;
      int32_t a = (int32_t)pop_int(S);
      int32_t b = (int32_t)pop_int(S);
      if (a == 0) c0_arith_error("C0 Arithmetic Error: Divide by zero.");
      if (a == -1 && b == -2147483648) c0_arith_error("overflow exception");
      push_int(S, (b/a));
      break;
    }

    case IREM: { 
      pc++;
      int32_t a = (int32_t)pop_int(S);
      int32_t b = (int32_t)pop_int(S);
      if (a == 0) c0_arith_error("C0 Arithmetic Error: Divide by zero.");
      if (a == -1 && b == -2147483648) c0_arith_error("overflow exception");
      push_int(S, (b%a));
      break;
    }

    case IAND: { 
      pc++;
      int32_t a = (int32_t)pop_int(S);
      int32_t b = (int32_t)pop_int(S);
      push_int(S, (b&a));
      break;
    }

    case IOR: {
      pc++;
      int32_t a = (int32_t)pop_int(S);
      int32_t b = (int32_t)pop_int(S);
      push_int(S, (b|a));
      break;
    }

    case IXOR: {
      pc++;
      int32_t a = (int32_t)pop_int(S);
      int32_t b = (int32_t)pop_int(S);
      push_int(S, (b^a));
      break;
    }

    case ISHR: {
      pc++;
      int32_t a = (int32_t)pop_int(S);
      int32_t b = (int32_t)pop_int(S);
      if (a < 0 || 32 <= a) c0_arith_error("C0 Arithmetic Error: rshift should in range of [0, 32)");
      push_int(S, (b >> a));
      break;
    }

    case ISHL: {
      pc++;
      int32_t a = (int32_t)pop_int(S);
      int32_t b = (int32_t)pop_int(S);
      if (a < 0 || 32 <= a) c0_arith_error("C0 Arithmetic Error: lshift should in range of [0, 32)");
      push_int(S, (b << a));
      break;
    }  


    /* Pushing constants */

    case BIPUSH: { 
      pc++;
      int32_t i = (int32_t)(signed char)P[pc];
      push_int(S, i);
      pc++;
      break;
    }

    case ILDC: {  
      // pc++;
      int32_t o1 = (int32_t)P[pc+1]; // maybe replace 32 with 16
      int32_t o2 = (int32_t)P[pc+2];
      uint16_t index = (o1 << 8) | o2; 
      int32_t x =  (int32_t)bc0->int_pool[index];
      push_int(S, x);
      pc += 3; 
      break;
    }

    case ALDC: { // aldc <c1,c2> S -> S, a:*  address ("reference")
      uint16_t o1 = (uint16_t)P[pc+1];
      uint16_t o2 = (uint16_t)P[pc+2];
      uint16_t index = (o1 << (uint16_t)8) | o2; 
      void* x = &(bc0->string_pool[index]); //cast to void
      push_ptr(S, x);
      // push_int(S, (int32_t)x);
      pc += 3; 
      break;
    }

    case ACONST_NULL: {
      pc++;
      push_ptr(S, NULL);  
      // c0v_push(S, NULL);
      break;
    }


    /* Operations on local variables */

    case VLOAD: {
      // read byte in position after opcode (pc+1)
      c0v_push(S, V[P[pc+1]]);
      pc += 2;
      break;
    }

    case VSTORE: {
      V[P[pc+1]] = c0v_pop(S);
      pc += 2;
      break;
    }

    /* Assertions and errors */

    case ATHROW: { //probably correct
      pc++;
      char* a = (char*)pop_ptr(S);
      c0_user_error(a);
      break;
    }

    case ASSERT: { 
      pc++;
      char* a = (char*)pop_ptr(S);
      // int x = val2int(c0v_pop(S));
      if (pop_int(S) == 0) c0_assertion_failure(a);
      break;
    }


    /* Control flow operations */

    case NOP: {
      pc++;
      break;
    }

    case IF_CMPEQ: {
      if (val_equal(c0v_pop(S), c0v_pop(S))) {
        int32_t o1 = (int32_t)P[pc+1];
        int32_t o2 = (int32_t)P[pc+2];
        pc = pc+(o1<<8|o2); 
      } else {
        pc += 3;
      }
       
      break;
    }

    case IF_CMPNE: {
      if (!val_equal(c0v_pop(S), c0v_pop(S))) {
        int32_t o1 = (int32_t)P[pc+1];
        int32_t o2 = (int32_t)P[pc+2];
        pc = pc+(o1<<8|o2); 
      } else {
        pc += 3;
      }
       
      break;
    }


    case IF_ICMPLT: {
      // bttom stack value > top stack value
      if (pop_int(S) > pop_int(S)) {
        int32_t o1 = (int32_t)P[pc+1];
        int32_t o2 = (int32_t)P[pc+2];
        pc = pc+(o1<<8|o2); 
      } else {
        pc += 3;
      }
       
      break;
    }

    case IF_ICMPGE: {
      if (pop_int(S) <= pop_int(S)) {
        int32_t o1 = (int32_t)P[pc+1];
        int32_t o2 = (int32_t)P[pc+2];
        pc = pc+(o1<<8|o2); 
      } else {
        pc += 3;
      }
       
      break;
    }

    case IF_ICMPGT: {
      if (pop_int(S) < pop_int(S)) {
        int32_t o1 = (int32_t)P[pc+1];
        int32_t o2 = (int32_t)P[pc+2];
        pc = pc+(o1<<8|o2); 
      } else {
        pc += 3;
      }
       
      break;
    }


    case IF_ICMPLE: {
      if (pop_int(S) >= pop_int(S)) {
        int32_t o1 = (int32_t)P[pc+1];
        int32_t o2 = (int32_t)P[pc+2];
        pc = pc+(o1<<8|o2); 
      } else {
        pc += 3;
      }
       
      
      break;
    }

    case GOTO: {
      // pc++;
      int32_t o1 = (int32_t)P[pc+1];
      int32_t o2 = (int32_t)P[pc+2];
      size_t target = pc+(int16_t)(o1<<8|o2);

      // target < 0
      // ubyte max = bc0->function_pool[0].code_length;
      // if (target < (size_t)max) c0_user_error("Error");
      pc = target;
      break;
    }


    /* Function call operations: */

    case INVOKESTATIC: {
      uint16_t o1 = (uint16_t)P[pc+1];
      uint16_t o2 = (uint16_t)P[pc+2];
      uint16_t index = (o1 << (uint16_t)8) | o2; 
      struct function_info fn = bc0->function_pool[index];
      
      uint16_t numArguments = fn.num_args;
      uint16_t numVariables = fn.num_vars;
      // (void)numVariables;
      pc += 3;
      //create frame to push into callStack
      frame *new_frame = xmalloc(sizeof(frame));
      new_frame->S = S;//c0v_stack_new();// S;
      new_frame->V = V; // xcalloc(numVariables, sizeof(c0_value));  
      new_frame->pc = pc;
      new_frame->P = P;

      push(callStack, (void*)new_frame);

      V = xmalloc(numVariables*sizeof(c0_value));  
      for (int16_t i = numArguments - 1; i >= 0; i--) {
        if (!c0v_stack_empty(S)) {
          V[i] = c0v_pop(S);
        } else {
          fprintf(stderr, "Error: Operand stack empty when copying arguments\n");
          exit(EXIT_FAILURE);
        }
      }
      // ASSERT(c0v_stack_empty(S));
      S = c0v_stack_new();// S;
      P = fn.code;
      pc = 0;
      break;
    }

    case INVOKENATIVE: {
      uint16_t o1 = (uint16_t)P[pc+1];
      uint16_t o2 = (uint16_t)P[pc+2];
      uint16_t index = (o1 << (uint16_t)8) | o2; 
      pc += 3;

      uint16_t numArgs = bc0->native_pool[index].num_args;
      c0_value val[numArgs];

      for (int16_t i = numArgs - 1; i >= 0; i--) {
        if (!c0v_stack_empty(S)) {
          val[i] = c0v_pop(S);
        } else {
          fprintf(stderr, "Error: Operand stack empty when copying arguments\n");
          exit(EXIT_FAILURE);
        }
      }

      uint16_t fIndex = bc0->native_pool[index].function_table_index;

      c0v_push(S, (*native_function_table[fIndex])(val));
      break;
    }

    /* Memory allocation and access operations: */

    case NEW: {
      uint8_t s = P[pc + 1];
      void *allocated_memory = xcalloc(s, sizeof(char));
      push_ptr(S, allocated_memory);
      pc += 2;
      break;
    }

    case IMLOAD: {
      void *a = pop_ptr(S);
      if (a == NULL) c0_memory_error("Error: Tried to load a value from a NULL memory address");
      int32_t value = *((int32_t *)a);
      push_int(S, value);
      pc++;
      break;
    }

    case IMSTORE:{
      int32_t x = pop_int(S);
      void *a = pop_ptr(S);
      if (a == NULL) c0_memory_error("Error: Tried to load a value from a NULL memory address");
      *((int32_t *) a) = x;
      pc++;
      break;
    }
    case AMLOAD: { //fix
      /* Load address from array */
      void **a = pop_ptr(S);
      // int32_t i = pop_int(S);
      if (a == NULL) c0_memory_error("Error: Tried to load a value from a NULL memory address");
      push_ptr(S, (*a));// [i]);
      pc++;
      break;
    }
    case AMSTORE: { //fix
      /* Store address into array */
      void **a = pop_ptr(S);
      if (a == NULL) c0_memory_error("Error: Tried to load a value from a NULL memory address");
      void *b = pop_ptr(S);
      if (b == NULL) c0_memory_error("Error: Tried to load a value from a NULL memory address");
      *a = b;
      // ((void **) a) = pop_ptr(S);
      pc++;
      break;
    }

    case CMLOAD: {
      /* Load character from memory */
      void *a = pop_ptr(S);
      if (a == NULL) c0_memory_error("Error: Tried to load a value from a NULL memory address");
      push_int(S, (int32_t) (*((char *) a)));
      pc++;
      break;
    }

    case CMSTORE: {
      /* Store character into memory */
      int32_t c = pop_int(S);
      void *a = pop_ptr(S);
      if (a == NULL) c0_memory_error("Error: Tried to load a value from a NULL memory address");
      *((char *) a) = (char) (c & 0x7F);
      pc++;
      break;
    }

    case AADDF: {
      /* Add offset to address */
      ubyte i = (ubyte)P[pc+1];
      void *a = pop_ptr(S);
      if (a == NULL) c0_memory_error("Error: Tried to load a value from a NULL memory address");
      push_ptr(S, ((char *) a) + i);
      pc += 2;
      break;
    }


    /* Array operations: */

    case NEWARRAY: { //ask
      /* Create new array of given size */
      int32_t size = (int32_t)(signed char)P[pc+1];
      int32_t n = pop_int(S);
      if(n < 0) c0_memory_error("Error: Negative array value");
      c0_array a;
      a.count = n;//num of elem
      a.elt_size = size; //sizeof(elem)
      a.elems = xcalloc((size_t)n, sizeof(void *));
      push_ptr(S, (void*)&a);
      pc += 2;
      break;
    }

    case ARRAYLENGTH:{
      /* Get length of array */
      c0_array *a = (c0_array*) pop_ptr(S);
      if (a == NULL) c0_memory_error("Error: Tried to load a value from a NULL memory address");
      push_int(S, a->count);
      pc++;
      break;
    }

    case AADDS:  {
      /* Add two addresses */
      int32_t b = pop_int(S);
      c0_array *a = (c0_array*) pop_ptr(S);
      if (a == NULL) c0_memory_error("Error: Tried to load a value from a NULL memory address");
      if (b < 0 || a->count < (uint32_t)b) c0_memory_error("Error: invalid index");

      char *result = ((char*)a->elems + a->elt_size * b);
      push_ptr(S, (void*)result);
      pc++;
      break;
    }


    /* BONUS -- C1 operations */

    case CHECKTAG:

    case HASTAG:

    case ADDTAG:

    case ADDROF_STATIC:

    case ADDROF_NATIVE:

    case INVOKEDYNAMIC:

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}

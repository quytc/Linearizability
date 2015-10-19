#include <caml/mlvalues.h>
#include <time.h>

CAMLprim value
caml_get_time(value unit)
{
  clock_t c; /* clock = unsigned long and in ocaml long = int, so no allocation */
  c = clock();
  return Val_long(c);
}

CAMLprim value
caml_delta_to_usec(value t)
{
  return Val_long( 1000000.0 * Long_val(t) / CLOCKS_PER_SEC );
}


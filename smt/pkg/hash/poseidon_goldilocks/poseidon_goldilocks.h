#ifndef POSEIDON_GOLDILOCKS_H
#define POSEIDON_GOLDILOCKS_H

/* Warning, this file is autogenerated by cbindgen. Don't modify this manually. */

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct Buffer {
  uint64_t *data;
  uintptr_t len;
} Buffer;

struct Buffer rustPoseidongoldHash(struct Buffer input_ptr);

void free_buf(struct Buffer buf);

#endif  /* POSEIDON_GOLDILOCKS_H */
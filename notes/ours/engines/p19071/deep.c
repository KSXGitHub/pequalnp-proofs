/* Solver-free exhaustive check of the LOOSE FanInTwo model on the one-a-side promise.
 *
 * Column view (see reach.py): on the 16 promise rows r = 4u+v every wire has a 16-bit
 * column.  Input columns are 0xF<<4u and 0x1111<<v.  A gate's column is ~a, a&b or a|b of
 * earlier columns, or the constant 0 (an out-of-range operand, or `or []`) or 0xFFFF
 * (`and []`, `not []`).  `Represents A C` with the output wire carrying the column `target`
 * is exactly: some wire's column equals target.  Because 0 and 0xFFFF are useless as
 * operands (0&a=0, 0|a=a, ~0=0xFFFF, 0xFFFF&a=a, 0xFFFF|a=0xFFFF, ~0xFFFF=0) and a
 * duplicate column is useless, a SHORTEST derivation adds only columns that are nonzero and
 * new; and target (858) is neither 0, nor 0xFFFF, nor an input column, so it is a gate.
 * Hence: least FanInTwo size = least number of ~/&/| steps reaching target from the eight
 * input columns, which is what this file enumerates exhaustively.
 *
 * Input: states4.bin, every reachable set of 4 added columns (from export4.py).
 * For each, this searches the remaining 3 steps.  argv[1] = target, argv[2] = budget
 * (3 for the 7-gate question, 2 for the 6-gate question, as a control).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static uint16_t TARGET, NTARGET;

/* one step from avail reaches TARGET? */
static int reach1(const uint16_t *a, int n) {
  for (int i = 0; i < n; i++) {
    if ((uint16_t)(~a[i]) == TARGET) return 1;
    for (int j = i + 1; j < n; j++) {
      if ((uint16_t)(a[i] & a[j]) == TARGET) return 1;
      if ((uint16_t)(a[i] | a[j]) == TARGET) return 1;
    }
  }
  return 0;
}

/* two steps from avail reach TARGET?
 *   target in S1(avail), or ~target in S1(avail), or
 *   some g in S1(avail) and b in avail with g&b == target or g|b == target.
 * (Those are all the ways the second step can name the first one; a second step that
 * names only wires of avail is the "target in S1(avail)" case.) */
static int reach2(const uint16_t *a, int n) {
  uint16_t s1[512];
  int m = 0;
  for (int i = 0; i < n; i++) {
    uint16_t t = (uint16_t)~a[i];
    if (t == TARGET) return 1;
    s1[m++] = t;
    for (int j = i + 1; j < n; j++) {
      uint16_t x = (uint16_t)(a[i] & a[j]);
      uint16_t y = (uint16_t)(a[i] | a[j]);
      if (x == TARGET || y == TARGET) return 1;
      s1[m++] = x;
      s1[m++] = y;
    }
  }
  for (int k = 0; k < m; k++) if (s1[k] == NTARGET) return 1;
  /* b must be a subset of target for the OR case, a superset for the AND case */
  uint16_t sub[64], sup[64];
  int ns = 0, np = 0;
  for (int i = 0; i < n; i++) {
    if ((uint16_t)(a[i] & (uint16_t)~TARGET) == 0) sub[ns++] = a[i];
    if ((uint16_t)(TARGET & (uint16_t)~a[i]) == 0) sup[np++] = a[i];
  }
  for (int t = 0; t < ns; t++) {
    uint16_t b = sub[t];
    for (int k = 0; k < m; k++) if ((uint16_t)(s1[k] | b) == TARGET) return 1;
  }
  for (int t = 0; t < np; t++) {
    uint16_t b = sup[t];
    for (int k = 0; k < m; k++) if ((uint16_t)(s1[k] & b) == TARGET) return 1;
  }
  return 0;
}

/* three steps from avail reach TARGET? */
static int reach3(const uint16_t *a, int n) {
  if (reach2(a, n)) return 1;
  uint16_t b[32];
  memcpy(b, a, (size_t)n * sizeof(uint16_t));
  for (int i = 0; i < n; i++) {
    uint16_t cs[3];
    int nc;
    for (int j = i; j < n; j++) {
      if (j == i) { cs[0] = (uint16_t)~a[i]; nc = 1; }
      else { cs[0] = (uint16_t)(a[i] & a[j]); cs[1] = (uint16_t)(a[i] | a[j]); nc = 2; }
      for (int c = 0; c < nc; c++) {
        b[n] = cs[c];
        if (reach2(b, n + 1)) return 1;
      }
    }
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: deep TARGET BUDGET [states4.bin]\n"); return 1; }
  TARGET = (uint16_t)strtol(argv[1], NULL, 0);
  NTARGET = (uint16_t)~TARGET;
  int budget = atoi(argv[2]);
  const char *path = (argc > 3) ? argv[3] : "states4.bin";
  FILE *fh = fopen(path, "rb");
  if (!fh) { perror(path); return 1; }
  fseek(fh, 0, SEEK_END);
  long bytes = ftell(fh);
  fseek(fh, 0, SEEK_SET);
  long nst = bytes / 8;
  uint16_t *st = malloc((size_t)bytes);
  if (fread(st, 1, (size_t)bytes, fh) != (size_t)bytes) { fprintf(stderr, "short read\n"); return 1; }
  fclose(fh);
  printf("target=0x%04x budget=%d states=%ld (each 4 added columns, 12 available)\n",
         TARGET, budget, nst);
  uint16_t avail[32];
  avail[0] = 0x000F; avail[1] = 0x00F0; avail[2] = 0x0F00; avail[3] = 0xF000;
  avail[4] = 0x1111; avail[5] = 0x2222; avail[6] = 0x4444; avail[7] = 0x8888;
  long found = 0;
  for (long s = 0; s < nst; s++) {
    for (int k = 0; k < 4; k++) avail[8 + k] = st[4 * s + k];
    int hit = (budget == 1) ? reach1(avail, 12)
            : (budget == 2) ? reach2(avail, 12)
                            : reach3(avail, 12);
    if (hit) {
      found++;
      if (found <= 3) {
        printf("HIT at state %ld: cols %04x %04x %04x %04x\n", s,
               st[4*s], st[4*s+1], st[4*s+2], st[4*s+3]);
      }
    }
    if ((s & 0xFFFFF) == 0) { printf("  .. %ld/%ld found=%ld\n", s, nst, found); fflush(stdout); }
  }
  printf("RESULT: budget=%d total gates=%d hits=%ld\n", budget, 4 + budget, found);
  if (found == 0) printf("RESULT: EXHAUSTED, NO circuit with at most %d gates\n", 4 + budget);
  return 0;
}

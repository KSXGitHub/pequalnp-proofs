/* For EVERY 16-bit target, is it reachable from the eight promise input columns in at most
 * 5, and in at most 6, ~/&/| steps?  (Same column model as deep.c / reach.py.)
 *
 * Union over every depth-4 state A of S1(A) is exactly the set of targets of least depth
 * at most 5: a target of least depth k <= 5 lies in S1 of some depth-(k-1) state, and any
 * such state extends to a depth-4 state (which only enlarges S1).  Likewise the union over
 * depth-5 states gives least depth at most 6.
 *
 * Used to pick calibration masks: a mask the scan leaves unmarked at 6 but that the CNF
 * engine solves at 7 exercises deep.c's depth-7 path on a KNOWN POSITIVE.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static unsigned char m5[65536], m6[65536];

int main(int argc, char **argv) {
  const char *path = (argc > 1) ? argv[1] : "states4.bin";
  FILE *fh = fopen(path, "rb");
  if (!fh) { perror(path); return 1; }
  fseek(fh, 0, SEEK_END); long bytes = ftell(fh); fseek(fh, 0, SEEK_SET);
  long nst = bytes / 8;
  uint16_t *st = malloc((size_t)bytes);
  if (fread(st, 1, (size_t)bytes, fh) != (size_t)bytes) return 1;
  fclose(fh);
  uint16_t a[16];
  a[0] = 0x000F; a[1] = 0x00F0; a[2] = 0x0F00; a[3] = 0xF000;
  a[4] = 0x1111; a[5] = 0x2222; a[6] = 0x4444; a[7] = 0x8888;
  for (long s = 0; s < nst; s++) {
    for (int k = 0; k < 4; k++) a[8 + k] = st[4 * s + k];
    /* S1 of the 12 available columns */
    uint16_t s1[256]; int m = 0;
    for (int i = 0; i < 12; i++) {
      uint16_t t = (uint16_t)~a[i]; m5[t] = 1; m6[t] = 1; s1[m++] = t;
      for (int j = i + 1; j < 12; j++) {
        uint16_t x = (uint16_t)(a[i] & a[j]), y = (uint16_t)(a[i] | a[j]);
        m5[x] = 1; m5[y] = 1; m6[x] = 1; m6[y] = 1;
        s1[m++] = x; s1[m++] = y;
      }
    }
    for (int c = 0; c < m; c++) {
      a[12] = s1[c];
      for (int i = 0; i < 13; i++) {
        m6[(uint16_t)~a[i]] = 1;
        for (int j = i + 1; j < 13; j++) {
          m6[(uint16_t)(a[i] & a[j])] = 1;
          m6[(uint16_t)(a[i] | a[j])] = 1;
        }
      }
    }
    if ((s & 0x3FFFF) == 0) { fprintf(stderr, "  .. %ld/%ld\n", s, nst); }
  }
  long c5 = 0, c6 = 0;
  for (int t = 0; t < 65536; t++) { c5 += m5[t]; c6 += m6[t]; }
  printf("targets with least depth <= 5: %ld ; <= 6: %ld ; > 6: %ld\n", c5, c6, 65536 - c6);
  printf("target 858: le5=%d le6=%d\n", m5[858], m6[858]);
  { FILE *b = fopen("m5.bin","wb"); fwrite(m5,1,65536,b); fclose(b);
    b = fopen("m6.bin","wb"); fwrite(m6,1,65536,b); fclose(b); }
  FILE *o = fopen("gt6.txt", "w");
  for (int t = 0; t < 65536; t++) if (!m6[t]) fprintf(o, "%d\n", t);
  fclose(o);
  printf("wrote the targets of least depth > 6 to gt6.txt\n");
  return 0;
}

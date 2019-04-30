#include <stdint.h>
#include <stdio.h>

uint64_t gcd(uint64_t x, uint64_t y) {
  while ((x>0) && (y>0) && (x != y)) {
    if (x > y)
      x = x-y;
    else
      y = y-x;
  }
  return x;
}

int64_t sqrt(int64_t x) {
  uint64_t y = 0;
  uint64_t sq = 0;
  while (sq < x) {
    y += 1;
    sq = y * y;
  }
  return y;
}

uint64_t modular_pow(uint64_t base, uint64_t exponent, uint64_t modulus) {
  if (modulus == 1) return 0;
  uint64_t result = 1;
  base = base % modulus;
  while (exponent > 0) {
    if ((exponent % 2) == 1) {
      result = (result * base) % modulus;
    }
    exponent = exponent >> 1;
    base = (base * base) % modulus;
  }
  return result;
}


uint64_t binary_search_buggy(uint64_t * buffer, uint64_t length, uint64_t value) {
  uint64_t left = 0;
  uint64_t right = length-1;
  while (left < right) {
    uint64_t middle = (right+left)/2;
    if (buffer[middle] == value)
      return middle;
    if (buffer[middle] < value)
      left = middle;
    else
      right = middle;
  }
  return length;
}

uint8_t binary_search_buggy2(uint64_t * buffer, uint8_t length, uint64_t value) {
  uint8_t left = 0;
  uint8_t right = length-1;
  printf("Size %d\n", sizeof(uint8_t));
  while (left <= right) {
    uint8_t sum = right+left;
    uint8_t middle = (sum)/2;
    printf("left right left+right %ld, %ld, %ld\n", left, right, sum);
    printf("middle = %ld\n", middle);
    if (buffer[middle] == value)
      return middle;
    if (buffer[middle] < value)
      left = middle + 1;
    else
      right = middle - 1;
  }
  return length;
}

uint64_t binary_search_ok(uint64_t * buffer, uint64_t length, uint64_t value) {
  uint64_t left = 0;
  uint64_t right = length-1;
  uint64_t middle;
  while (left < right) {
    middle = left + (right-left)/2;
    if (buffer[middle] < value)
      left = middle + 1;
    else
      right = middle - 1;
  }
  if (buffer[middle] == value)
    return middle;
  return length;
}

uint8_t binary_search_ok2(uint64_t * buffer, uint8_t length, uint64_t value) {
  uint8_t left = 0;
  uint8_t right = length-1;
  uint8_t middle;
  while (left <= right) {
    middle = left + (right-left)/2;
    printf("left, middle, right = %ld, %ld, %ld\n", left, middle, right);
    if (buffer[middle] < value)
      left = middle + 1;
    else
      right = middle - 1;
  }
  if (buffer[middle] == value)
    return middle;
  return length;
}

int main(int argc, char ** argv) {
  printf("CGD 6 9 %ld\n", gcd(6, 9));
  printf("CGD 12 18 %ld\n", gcd(12, 18));
  for (int i=0; i<20; i++) {
    printf("SQRT %d %ld\n", i, sqrt(i));
  }
  printf("POW MOD 3^3 mod 4 = 27 mod 4 = 3 ? %ld\n", modular_pow(3, 3, 4));

  uint64_t buffer[255];
  buffer[0] = 0; buffer[1] = 10;
  // binary_search_buggy(buffer, 2, 1);
  printf("SEARCH 0 = %ld\n", binary_search_buggy(buffer, 2, 0));
  for (int i=0; i<255; i++) {
    buffer[i] = i;
  }
  // printf("SEARCH 200 = %ld\n", binary_search_buggy2(buffer, 255, 200));
  printf("SEARCH 200 = %ld\n", binary_search_ok2(buffer, 255, 200));
  
  return 0;
}

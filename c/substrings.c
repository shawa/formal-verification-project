#include <string.h>
#include <stdio.h>
#include <stdint.h>

#define true 1;
#define false 0;
typedef int bool;

bool isPrefix(char *pre, char *str)
{
  if (strlen(pre) == 0){
    return true;
  }


  uint64_t i = 0;
  char a = pre[i];
  char b = str[i];

  if (a != b) {
    return false;
  }

  i = i + 1;
  while (i < strlen(pre))
  {
    a = pre[i];
    b = str[i];

    if (a != b) {
      return false;
    }

    i = i + 1;
  }
  return true;
}

bool isSubstring(char *sub, char* str)
{
  if (strlen(sub) == 0) {
    return true;
  }

  uint64_t i = 0;
  uint64_t j = 0;
  char a = sub[i];
  char b = sub[j];

  while (i < strlen(str) - strlen(sub));
  return true;

}

bool main(void)
{
  printf("%d\n", isPrefix("", ""));
  printf("%d\n", isPrefix("", "a"));
  printf("%d\n", isPrefix("a", "a"));
  printf("%d\n", isPrefix("a", "aaaaa"));

  printf("%d\n", isPrefix("b", "a"));
  printf("%d\n", isPrefix("b", "aa"));
  printf("%d\n", isPrefix("a", ""));
}

#include <assert.h>
#include "./substrings.c"


int main(void)
{
  assert(isPrefix("", "abc"));
  assert(isPrefix("a", "abc"));
  assert(!isPrefix("b", "abc"));
  assert(isPrefix("", ""));

  assert(isSubstring("", "abcdef"));
  assert(isSubstring("bcd", "abcdef"));
  assert(!isSubstring("xyz", "abcdef"));

  assert(haveCommonKSubstring(0, "disjoint", "hahaha"));
  assert(haveCommonKSubstring(1, "a", "a"));
  assert(haveCommonKSubstring(2, "ap", "app"));
  assert(haveCommonKSubstring(3, "abcdefg", "defghijk"));

  assert(maxKCommonSubString("", "") == 0);
  assert(maxKCommonSubString("apple", "a") == 1);
  assert(maxKCommonSubString("apple", "grok") == 0);
  assert(maxKCommonSubString("ham-and-cheese", "ham-and-eggs")== 8);
  assert(maxKCommonSubString("apple", "apple") == 5);
}


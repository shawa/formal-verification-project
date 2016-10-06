#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>


char *slice(char* str, uint64_t start, uint64_t end)
{

  char slicedLength = (end-start) + 1;
  char *result = malloc(sizeof(char) * (slicedLength + 1));
  memcpy(result, str+start, slicedLength + 1);
  *(result + slicedLength) = '\0';
  return result;
}

// The following method should return true if and only if pre is a prefix of
// str. That is, str starts with pre.
bool isPrefix(char *pre, char *str)
{
  if (strlen(pre) == 0) {
    // following from the logic presented in the description
    // for maxCommonSubstringLength, and sets, it holds that
    // the null string is a prefix of any string, including itself
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

// The following method should return true if and only if sub is a substring of
// str. That is, str contains sub.
bool isSubstring(char *sub, char *str)

{
  if (strlen(sub) == 0){
    // similarly to isPrefix, the null string is a substring of every string,
    // including itself
    return true;
  }
  uint64_t i = 0;
  uint64_t j = 0;
  bool subIsPrefixOfSlice;
  while (i < strlen(str) - strlen(sub))
    // if the searched-for substring is of length n,
    // don't try to search for prefixes that begin after the nth position
    // so if we have a length 3 substring candidate, and a length 5 string,
    // there's no reason to try and keep testing if we go past the 5-3=2nd position
    //  | a | b | c | d | e |
    //                ^^^^^^---not within search space
    //
    //  d | e | f               -> i = 0        => continue searching
    //      d | e | f           -> i = 1        => continue searching
    //          d | e | f       -> i = 2        => continue searching
    //              d | e | f   -> i = 3, i > 2 => FAIL
  {
    subIsPrefixOfSlice = isPrefix(sub, str+i);
    if (subIsPrefixOfSlice) {
      return true;
    }

    i = i + 1;
  }

  return false;
}


// The following method should return true if and only if str1
// and str1 have a common substring of length k.
bool haveCommonKSubstring(uint64_t k, char  *str1, char *str2)
{
  char *candidate;
  char *longer;
  char *shorter;
  uint64_t i = 0;
  uint64_t j = 0;

  bool isAPrefix;
  //taking cues from sets, the null string "" is a substring of every string
  if (k == 0) {
    return true;
  }


  if (strlen(str1) < strlen(str2)) {
    shorter = str1;
    longer = str2;
  } else {
    shorter = str2;
    longer = str1;
  }

  while (i <= strlen(shorter) - k)
  {
    candidate = slice(shorter, i, i+k-1);
    while (j <= strlen(longer) - k)
    {
      isAPrefix = isPrefix(candidate, longer);
      if (isAPrefix) {
        return true;
      }
      j = j + 1;
    }
    i = i + 1;
  }

  free(candidate);
  return false;
}


uint64_t maxKCommonSubString(char *str1, char *str2)
{
  char *shorter;
  char *longer;
  bool thereIsACommonSubstring;
  uint64_t k;
  k = 0;
  if (strlen(str1) <= strlen(str2)) {
    shorter = str1;
    longer = str2;
  } else {
    shorter = str2;
    longer = str1;
  }


  while (k <= strlen(shorter))
  {
   thereIsACommonSubstring = haveCommonKSubstring(k, shorter, longer);
   if (!thereIsACommonSubstring) {
    return k;
   } else {
    break;
   }

   k = k + 1;

  }
  return k;
}


int main(void)
{
  return 1;
}

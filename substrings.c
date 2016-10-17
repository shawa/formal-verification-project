#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

typedef char* string;
typedef uint64_t nat;

char *__slice__(char* str, int start, int end)
{
	int len = end - start + 1;

	char *res = malloc(sizeof(char) * len + 1);
	res[len] = '\0';

	memcpy(res, str+start, len);

	return res;
}
// The following method should return true if and only if pre is a prefix of
// str. That is, str starts with pre.
bool isPrefix(string pre, string str)
{
  if (strlen(pre) == 0) {
    // following from the logic presented in the description
    // for maxCommonSubstringLength, and sets, it holds that
    // the null string is a prefix of any string, including itself
    return true;
  }

 nat i = 0;
 char a;
 char b;
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
bool isSubstring(string sub, string str)
{
  if (strlen(sub) == 0){
    // similarly to isPrefix, the null string is a substring of every string,
    // including itself
    return true;
  }
 nat i = 0;
  while (i <= (strlen(str) - strlen(sub)))
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
 string slice = __slice__(str, i, strlen(str));
 bool subIsPrefixOfSlice = isPrefix(sub, slice);

    if (subIsPrefixOfSlice) {
      return true;
    }

    i = i + 1;
  }

  return false;
}


// The following method should return true if and only if str1
// and str1 have a common substring of length k.
bool haveCommonKSubstring(nat k, string str1, string str2)
{
 string candidate;
 string longer;
 string shorter;

 nat i = 0;
 nat j = 0;

 bool isASubstring;

  //taking cues from sets, the null string "" is a substring of every string
  if (k == 0) {
    return true;
  }

  if (k > strlen(str1) || k > strlen(str2)) {
    // what are you at?
    return false;
  }


  while (i <= strlen(str1) - k)
  {
    candidate = __slice__(str1, i, i+k-1);
    isASubstring = isSubstring(candidate, str2);

    if (isASubstring) {
      return true;
    }

    i = i + 1;
  }
  return false;
}



nat maxKCommonSubString(string str1, string str2)
{
 string shorter;
 string longer;
 bool thereIsACommonSubstring = false;
 nat k = 0;

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
    if (thereIsACommonSubstring) {
      k = k + 1;
    } else {
      break;
    }
  }
  return k - 1;
}

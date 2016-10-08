// The following method should return true if and only if pre is a prefix of
// str. That is, str starts with pre.
method isPrefix(pre: string, str: string) returns (res: bool)
  requires |pre| <= |str|;  //sub can be contained in str
{
  if (|pre| == 0) {
    // following from the logic presented in the description
    // for maxCommonSubstringLength, and sets, it holds that
    // the null string is a prefix of any string, including itself
    return true;
  }

  var i: nat := 0;
  var a: char := pre[i];
  var b: char := str[i];

  if (a != b) {
    return false;
  }

  i := i + 1;
  while (i < |pre|)
    decreases |pre| - i;
    invariant 0 <= i <= |pre|
    invariant a in pre;
    invariant b in str;
  {
    a := pre[i];
    b := str[i];
    if (a != b) {
      return false;
    }
    i := i + 1;
  }

  return true;
}

// The following method should return true if and only if sub is a substring of
// str. That is, str contains sub.
method isSubstring(sub: string, str: string) returns (res: bool)
  requires |sub| <= |str|; // sub can be contained in str
{
  if (|sub| == 0){
    // similarly to isPrefix, the null string is a substring of every string,
    // including itself
    return true;
  }
  var i: nat := 0;
  var j: nat := 0;
  while (i < |str| - |sub|)
    decreases |str| - |sub| - i;
    invariant 0 <= i <= (|str| - |sub|);
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
    var subIsPrefixOfSlice: bool := isPrefix(sub, str[i..]);
    if (subIsPrefixOfSlice) {
      return true;
    }

    i := i + 1;
  }

  return false;
}


// The following method should return true if and only if str1
// and str1 have a common substring of length k.
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
  requires k <= |str1| && k <= |str2|;
{
  var candidate: string;
  var longer: string;
  var shorter: string;
  var i: nat := 0;
  var j: nat := 0;
  var isAPrefix: bool;

  //taking cues from sets, the null string "" is a substring of every string
  if (k == 0) {
    return true;
  }


  if (|str1| < |str2|) {
    shorter := str1;
    longer := str2;
  } else {
    shorter := str2;
    longer := str1;
  }

  while (i <= |shorter| - k)
    decreases |shorter| - k - i;
    invariant i <= i+k-1;
  {
    candidate := shorter[i..i+k-1];
    while (j <= |longer| - k)
      decreases |longer| - k - j;
    {
      isAPrefix := isPrefix(candidate, longer);
      if (isAPrefix) {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}


method maxKCommonSubString(str1: string, str2: string) returns (k: nat)
  ensures k <= |str1| && k <= |str2|;
{
  var shorter: string;
  var longer: string;
  var thereIsACommonSubstring: bool;

  k := 0;
  if (|str1| <= |str2|) {
    shorter := str1;
    longer := str2;
  } else {
    shorter := str2;
    longer := str1;
  }


  while (k <= |shorter|)
    decreases |shorter| - k;
  {
   thereIsACommonSubstring := haveCommonKSubstring(k, shorter, longer);
   if (!thereIsACommonSubstring) {
    return k;
   } else {
    break;
   }

   k := k + 1;

  }
  return k;
}

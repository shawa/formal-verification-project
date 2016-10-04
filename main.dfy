// The following method should return true if and only if pre is a prefix of
// str. That is, str starts with pre.
method isPrefix(pre: string, str: string) returns (res:bool)
  requires |pre| <= |str|;  //sub can be contained in str
{
  if (|pre| == 0) {
    // following from the logic presented in the description
    // for maxCommonSubstringLength, and sets, it holds that
    // the null string is a prefix of any string, including itself
    return true;
  }

  var i := 0;
  var a := pre[i];
  var b := str[i];

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
method isSubstring(sub: string, str: string) returns (res:bool)
  requires |sub| <= |str|; // sub can be contained in str
{
  if (|sub| == 0){
    // similarly to isPrefix, the null string is a substring of every string,
    // including itself
    return true;
  }
  var i := 0;
  var j := 0;
  var a := sub[i];
  var b := str[j];

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
    var subIsPrefixOfSlice := isPrefix(sub, str[i..]);
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
  //taking cues from sets, the null string "" is a substring of every string
  if (k == 0) {
    return true;
  }

  //reduce our search space to the smaller of the two strings
  var shorter;
  var longer;
  if (|str1| <= |str2|) {
    shorter := str1;
    longer := str2;
  } else {
    longer := str1;
    shorter := str2;
  }


  var i := 0;
  var candidate;
  while (i <= |shorter| - k)
    invariant i <= i+k-1;
  {
    candidate := shorter[i..i+k-1];
  }

}

// The following method should return the natural number len which is equal to
// the length of the longest common substring of str1 and str2. Note that every two
// strings have a common substring of length zero.
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)

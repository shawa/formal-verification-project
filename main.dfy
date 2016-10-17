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
  var a: char;
  var b: char;
  while (i < |pre|)
    decreases |pre| - i;
    invariant 0 <= i <= |pre|
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
  while (i <= (|str| - |sub|))
    decreases |str| - |sub| - i;
    invariant 0 <= i;
    invariant i <= (|str| - |sub|) + 1;
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
    var slice: string := str[i..];
    var subIsPrefixOfSlice: bool := isPrefix(sub, slice);

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
  ensures (k > |str1| || k > |str2|) ==> found == false;
  ensures found == true ==> (k <= |str1| || k <= |str2|);
{
  var candidate: string;
  var longer: string;
  var shorter: string;

  var i: nat := 0;
  var j: nat := 0;

  var isASubstring: bool;

  //taking cues from sets, the null string "" is a substring of every string
  if (k == 0) {
    return true;
  }

  if (k > |str1| || k > |str2|) {
    // what are you at?
    return false;
  }


  while (i <= |str1| - k)
    decreases |str1| - k - i;
    invariant i <= i+k-1;
  {
    candidate := str1[i..i+k-1];
    isASubstring := isSubstring(candidate, str2);

    if (isASubstring) {
      return true;
    }

    i := i + 1;
  }
  return false;
}



method maxKCommonSubString(str1: string, str2: string) returns (k: nat)
  ensures k <= |str1|;
  ensures k <= |str2|;
  ensures (|str1| == 0 || |str2| == 0 ) ==> k == 0;
{
  var shorter: string;
  var longer: string;
  var thereIsACommonSubstring: bool := false;
  var i: nat := 0;

  if (|str1| <= |str2|) {
    shorter := str1;
    longer := str2;
  } else {
    shorter := str2;
    longer := str1;
  }

  while (i <= |shorter|)
    decreases |shorter| - i;
  {
    thereIsACommonSubstring := haveCommonKSubstring(i, shorter, longer);
    if (thereIsACommonSubstring) {
      i := i + 1;
    } else {
      return i;
    }
  }
}

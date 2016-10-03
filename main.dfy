// The following method should return true if and only if pre is a prefix of
// str. That is, str starts with pre.
method isPrefix(pre: string, str: string) returns (res:bool)
  requires |pre| > 0;
  requires |str| > 0;
  requires |pre| <= |str|;
{
  var i := 0;
  var a := pre[i];
  var b := str[i];

  if (a != b) {
   return false;
  }

  i := i + 1;

  while (i < |pre|)
    decreases |pre| - i;
    invariant a in pre;
    invariant b in str;
    invariant a == b;
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
  requires |sub| > 0;
  // sub is nonzero

  requires |str| > 0;
  // str is nonzero

  requires |sub| <= |str|;
  // sub can be contained in str

{
  var i := 0;
  var j := 0;
  var a := sub[i];
  var b := str[j];

  while (i < |sub| - |str|)
    decreases |str| - |str| - i;

    invariant i <= (|str| - |sub|);
    // if the searched-for substring is of length n,
    // don't try to search for prefixes that begin after the nth position
    // sub = ate, str = carat:
    //
    // | c | a | r | a | t |
    //
    // | 0 | 1 | 2 | 3 | 4 |
    //           i

    invariant 0 <= i <= |str|;

    invariant a in sub;
    invariant b in str;
    invariant |str[i..]| <= |str|;
  {
    var isAPrefix := isPrefix(sub, str[i..]);
    if (isAPrefix) {
      return true;
    }
    i := i + 1;
  }

  return false;
}

// The following method should return true if and only if str1
// and str1 have a common substring of length k.
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)

// The following method should return the natural number len which is equal to
// the length of the longest common substring of str1 and str2. Note that every two
// strings have a common substring of length zero.
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)

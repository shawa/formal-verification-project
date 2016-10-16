# CS4004 Project

## Implement in Dafny the following methods
The following method should return true if and only if pre is a prefix of str. That is, str starts with pre.
```dafny
method isPrefix(pre: string, str: string) returns (res:bool)
```

The following method should return true if and only if sub is a substring of str. That is, str contains sub.
```dafny
method isSubstring(sub: string, str: string) returns (res:bool)
```

The following method should return true if and only if str1 and str1 have a common substring of length k.
```dafny
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
```

The following method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
```dafny
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
```

## Notes
When implementing each of these methods you should make calls to the previous methods. Although this may not lead to the most optimal implementations, it will make verification easier.

In this part of the project you do not need to include any verification instructions. Only the program code.

Dafny may complain that your while loops may not terminate. You can ignore these warnings for now.

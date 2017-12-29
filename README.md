# data-word
Agda FFI bindings to Haskell ByteString and Word8.

## Word8
The following functions are supported: `_==_`, `_/=_`, `_xor_`, `_or_`, `_and_` and conversion to and from Nat.

## ByteString
A few common functions are supported: length, index, splitAt, pack, unpack, file I/O.
Strict and Lazy ByteStrings are supported.
Tested with bytestring-0.10.8.2.

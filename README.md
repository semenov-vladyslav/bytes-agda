# bytes
Agda FFI bindings to Haskell `ByteString` and `Word8`.

## `Word8`
The following functions are supported: `_==_`, `_/=_`, `_xor_`, `_or_`, `_and_` and conversion to and from `Nat`.

## `ByteString`
A few common functions are supported: `empty`, `null`, `length`, `unsafeIndex`, `unsafeSplitAt`, `_++_`, `pack`, `unpack`, file I/O.
`Strict` and `Lazy` `ByteString`s are supported.
Tested with bytestring-0.10.8.2.

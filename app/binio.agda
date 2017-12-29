module binio where

open import Data.Word8
import Data.ByteString as BS
import Data.ByteString.IO as BSIO
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (Vec; toList; tabulate)
open import Data.List using (List)
open import Data.Colist using (Colist; fromList)
open import Agda.Builtin.Nat using (Nat; zero; suc; _<_)
open import IO
open import Coinduction using (♯_)

{-
instance
  finN<N : {n : Nat} {f : Fin n} → IsTrue (toℕ f < n)
  finN<N {.(suc _)} {Fin.zero} = itis
  finN<N {.(suc _)} {Fin.suc f} = finN<N {_} {f}

fin256 : Fin 256 → Word8
fin256 f = fromNat (toℕ f) {{finN<N {256} {f}}}

b256 : Colist Word8
b256 = fromList (toList (tabulate {256} fin256))
-}

fin256 : Fin 256 → Word8
fin256 f = primWord8fromNat (toℕ f)

b256 : List Word8
b256 = toList (tabulate {256} fin256)

b256′ : Colist Word8
b256′ = fromList b256


-- main = run (writeBinaryFile "256.bin" b256)
-- main = run (♯ readBinaryFile "256.bin" >>= λ x → ♯ writeBinaryFile "256'.bin" x)
-- main = run (readFile "256.bin")

main = run (BSIO.writeBinaryFile′ "256.bin" b256)
-- main = run (BS.IO.writeBinaryFile′ "256'.bin" b256′)

-- main = run (BS.IO.writeBinaryFile′ "256.bin" b256 >> BS.IO.writeBinaryFile′ "256'.bin" b256′)

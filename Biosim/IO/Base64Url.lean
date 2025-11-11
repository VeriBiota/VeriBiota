import Init.Data.ByteArray

namespace Biosim
namespace IO
namespace Base64Url

private def alphabet : Array Char :=
  #['A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z',
    'a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z',
    '0','1','2','3','4','5','6','7','8','9','-','_']

@[inline] private def charAt (idx : Nat) : Char :=
  alphabet.get! idx

private def encodeTriple (a b c : UInt8) (acc : List Char) :
    List Char :=
  let a32 := UInt32.ofNat a.toNat
  let b32 := UInt32.ofNat b.toNat
  let c32 := UInt32.ofNat c.toNat
  let idx0 := (a32 >>> 2).toNat
  let idx1 := (((a32 &&& 0x03) <<< 4) ||| (b32 >>> 4)).toNat
  let idx2 := (((b32 &&& 0x0F) <<< 2) ||| (c32 >>> 6)).toNat
  let idx3 := (c32 &&& 0x3F).toNat
  charAt idx3 :: charAt idx2 :: charAt idx1 :: charAt idx0 :: acc

private def encodeDouble (a b : UInt8) (acc : List Char) :
    List Char :=
  let a32 := UInt32.ofNat a.toNat
  let b32 := UInt32.ofNat b.toNat
  let idx0 := (a32 >>> 2).toNat
  let idx1 := (((a32 &&& 0x03) <<< 4) ||| (b32 >>> 4)).toNat
  let idx2 := ((b32 &&& 0x0F) <<< 2).toNat
  charAt idx2 :: charAt idx1 :: charAt idx0 :: acc

private def encodeSingle (a : UInt8) (acc : List Char) :
    List Char :=
  let a32 := UInt32.ofNat a.toNat
  let idx0 := (a32 >>> 2).toNat
  let idx1 := ((a32 &&& 0x03) <<< 4).toNat
  charAt idx1 :: charAt idx0 :: acc

/-- Encode a byte array using URL-safe base64 without padding. -/
def encode (bytes : ByteArray) : String :=
  let data := bytes.data.toList
  let rec loop
      : List UInt8 → List Char → List Char
    | a :: b :: c :: rest, acc =>
        loop rest (encodeTriple a b c acc)
    | [a, b], acc =>
        encodeDouble a b acc
    | [a], acc =>
        encodeSingle a acc
    | [], acc => acc
  String.mk (List.reverse <| loop data [])

private def value? (c : Char) : Option UInt8 :=
  if 'A' ≤ c ∧ c ≤ 'Z' then
    some <| UInt8.ofNat (c.toNat - 'A'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then
    some <| UInt8.ofNat (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c ∧ c ≤ '9' then
    some <| UInt8.ofNat (c.toNat - '0'.toNat + 52)
  else if c = '-' then
    some 62
  else if c = '_' then
    some 63
  else
    none

/-- Decode a URL-safe base64 string (without padding) into bytes. -/
def decode (input : String) : Except String ByteArray := do
  let rec gather (chars : List Char) (acc : List UInt8) :
      Except String (List UInt8) :=
    match chars with
    | [] => pure (List.reverse acc)
    | c :: cs =>
        match value? c with
        | some v => gather cs (v :: acc)
        | none => Except.error s!"Invalid base64url character '{c}'"
  let values ← gather input.toList []
  let rec emit (vals : List UInt8) (output : List UInt8) :
      Except String (List UInt8) :=
    match vals with
    | v0 :: v1 :: v2 :: v3 :: rest =>
        let b0 : UInt8 :=
          UInt8.ofNat (((v0.toNat <<< 2) ||| (v1.toNat >>> 4)) &&& 0xFF)
        let b1 : UInt8 :=
          UInt8.ofNat ((((v1.toNat &&& 0x0F) <<< 4) ||| (v2.toNat >>> 2)) &&& 0xFF)
        let b2 : UInt8 :=
          UInt8.ofNat ((((v2.toNat &&& 0x03) <<< 6) ||| v3.toNat) &&& 0xFF)
        emit rest (b2 :: b1 :: b0 :: output)
    | [v0, v1, v2] =>
        let b0 : UInt8 :=
          UInt8.ofNat (((v0.toNat <<< 2) ||| (v1.toNat >>> 4)) &&& 0xFF)
        let b1 : UInt8 :=
          UInt8.ofNat ((((v1.toNat &&& 0x0F) <<< 4) ||| (v2.toNat >>> 2)) &&& 0xFF)
        pure (List.reverse (b1 :: b0 :: output))
    | [v0, v1] =>
        let b0 : UInt8 :=
          UInt8.ofNat (((v0.toNat <<< 2) ||| (v1.toNat >>> 4)) &&& 0xFF)
        pure (List.reverse (b0 :: output))
    | [] => pure (List.reverse output)
    | _ =>
        Except.error "Invalid base64url length"
  let bytesList ← emit values []
  pure <| ByteArray.mk bytesList.toArray

/-- Convert a standard Base64 string (with `+`, `/`, `=`) into URL-safe form without padding. -/
def fromStandard (std : String) : String :=
  let replaced :=
    std.replace "+" "-"
      |>.replace "/" "_"
      |>.trim
  replaced.dropRightWhile (· = '=')

end Base64Url
end IO
end Biosim

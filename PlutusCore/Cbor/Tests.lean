import PlutusCore.Cbor.Basic

namespace PlutusCore.Cbor
open PlutusCore.Cbor.CborInternal

/-- Convert a String of codepoint-as-byte characters to its `ByteArray` representation.
    Test-only helper: matches the historical convention where each Char in 0–255 stands
    for the byte with the same value (the same convention used by the UPLC `ByteString`
    domain wrapper). -/
private def s2ba (s : String) : ByteArray := ⟨(Char.toUInt8 <$> s.data).toArray⟩

-- ==============
-- =  Encoding  =
-- ==============

example : e₈ 7234295460216005990 = "deadbeef".toUTF8 := by rfl

example : splitToChunks .empty = [] := by rfl

example : splitToChunks (s2ba "1234567890123456789012345678901234567890123456789012345678901234") =
  [ s2ba "1234567890123456789012345678901234567890123456789012345678901234" ] := by native_decide

example : splitToChunks (s2ba "12345678901234567890123456789012345678901234567890123456789012345") =
  [ s2ba "1234567890123456789012345678901234567890123456789012345678901234"
  , s2ba "5"
  ] := by native_decide

example : splitToChunks (s2ba "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456") =
  [ s2ba "1234567890123456789012345678901234567890123456789012345678901234"
  , s2ba "1234567890123456789012345678901234567890123456789012345678901234"
  , s2ba "56"
  ] := by native_decide

example : encodeBytestring (s2ba "1234567890123456789012345678901234567890123456789012345678901234") =
  .some (s2ba ("\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234")) := by native_decide

example : encodeBytestring (s2ba "12345678901234567890123456789012345678901234567890123456789012345") =
  .some (s2ba ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x41"     ++ "5"
         ++ "\xFF")) := by native_decide

example : encodeBytestring (s2ba "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456") =
  .some (s2ba ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x42"     ++ "56"
         ++ "\xFF")) := by native_decide

example : encodeData (.I 12) = .some (s2ba "\x0c")     := by native_decide
example : encodeData (.I 42) = .some (s2ba "\x18\x2a") := by native_decide

example :
    encodeData (
      .Constr 0 [
        .Constr 0 [.I 1284531],
        .I 1739713998000
      ]
    ) = .some (s2ba "\xd8\x79\x9f\xd8\x79\x9f\x1a\x00\x13\x99\xb3\xff\x1b\x00\x00\x01\x95\x0f\x08\xec\xb0\xff") := by native_decide

example :
  encodeData (
    .Constr 0 [
      .I 144375414,
      .I 22710,
      .I 4387720097
    ]
  ) = .some (s2ba "\xd8\x79\x9f\x1a\x08\x9a\xfe\x76\x19\x58\xb6\x1b\x00\x00\x00\x01\x05\x87\x4b\xa1\xff") := by native_decide

-- Bignum encoding (magnitude ≥ 2^64) goes through `itos`, which must be big-endian (Spec B.6).
example : itos 258 = s2ba "\x01\x02" := by native_decide
-- Positive bignum: CBOR tag 2 (0xc2), then a 9-byte bytestring 01 00…00 for 2^64.
example : encodeData (.I 18446744073709551616) =
  .some (s2ba "\xc2\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00") := by native_decide
-- Negative bignum: CBOR tag 3 (0xc3); the encoded magnitude is -n-1 = 2^64.
example : encodeData (.I (-18446744073709551617)) =
  .some (s2ba "\xc3\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00") := by native_decide

-- ==============
-- =  Decoding  =
-- ==============

example :
    d₈ { input := s2ba "deadbeef", pos := 0 } =
    .some ({ input := s2ba "deadbeef", pos := 8 }, 7234295460216005990) := by native_decide

example :
    d₁ { input := s2ba "deadbeef", pos := 0 } =
    .some ({ input := s2ba "deadbeef", pos := 1 }, 100) := by native_decide

example : decodeBytestring (s2ba ("\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234")) =
  .some (s2ba "", s2ba "1234567890123456789012345678901234567890123456789012345678901234") := by native_decide

example : decodeData (s2ba "\x0C")     = .some (s2ba "", .I 12) := by native_decide
example : decodeData (s2ba "\x18\x2A") = .some (s2ba "", .I 42) := by native_decide

example : decodeData (s2ba "\xd8\x79\x9f\xd8\x79\x9f\x1a\x00\x13\x99\xb3\xff\x1b\x00\x00\x01\x95\x0f\x08\xec\xb0\xff\x34\x32")
    = .some (
        s2ba "42",
        .Constr 0 [
          .Constr 0 [.I 1284531],
          .I 1739713998000
        ]
      ) := by native_decide

example : decodeData (s2ba "\xd8\x79\x9f\x1a\x08\x9a\xfe\x76\x19\x58\xb6\x1b\x00\x00\x00\x01\x05\x87\x4b\xa1\xff\x43\x62\x6f\x72\x44\x61\x74\x61")
  = .some (
      s2ba "CborData",
      .Constr 0 [
        .I 144375414,
        .I 22710,
        .I 4387720097
      ]
  ) := by native_decide

-- Bignum decode: reads the big-endian bytestring back to 2^64 (round-trips with encoding above).
example : decodeData (s2ba "\xc2\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00") =
  .some (s2ba "", .I 18446744073709551616) := by native_decide

end PlutusCore.Cbor

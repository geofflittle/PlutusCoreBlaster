import PlutusCore.Cbor.Basic

namespace PlutusCore.Cbor
open PlutusCore.Cbor.CborInternal

-- ==============
-- =  Encoding  =
-- ==============

example : e₈ 7234295460216005990 = "deadbeef".toList := rfl

example : splitToChunks "" = [] := by native_decide

example : splitToChunks "1234567890123456789012345678901234567890123456789012345678901234" =
  [ "1234567890123456789012345678901234567890123456789012345678901234" ] := by native_decide

example : splitToChunks  "12345678901234567890123456789012345678901234567890123456789012345" =
  [ "1234567890123456789012345678901234567890123456789012345678901234"
  , "5"
  ] := by native_decide

example : splitToChunks "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456" =
  [ "1234567890123456789012345678901234567890123456789012345678901234"
  , "1234567890123456789012345678901234567890123456789012345678901234"
  , "56"
  ] := by native_decide

example : encodeBytestring "1234567890123456789012345678901234567890123456789012345678901234" =
  .some ("\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234") := by native_decide

example : encodeBytestring "12345678901234567890123456789012345678901234567890123456789012345" =
  .some ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x41"     ++ "5"
         ++ "\xFF") := by native_decide

example : encodeBytestring "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456" =
  .some ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x42"     ++ "56"
         ++ "\xFF") := by native_decide

example : encodeData (.I 12) = .some "\x0c"     := by simp [encodeData, encodeInt, encodeHead]
example : encodeData (.I 42) = .some "\x18\x2a" := by simp [encodeData, encodeInt, encodeHead]

example :
    encodeData (
      .Constr 0 [
        .Constr 0 [.I 1284531],
        .I 1739713998000
      ]
    ) = .some "\xd8\x79\x9f\xd8\x79\x9f\x1a\x00\x13\x99\xb3\xff\x1b\x00\x00\x01\x95\x0f\x08\xec\xb0\xff" := by native_decide

example :
  encodeData (
    .Constr 0 [
      .I 144375414,
      .I 22710,
      .I 4387720097
    ]
  ) = .some "\xd8\x79\x9f\x1a\x08\x9a\xfe\x76\x19\x58\xb6\x1b\x00\x00\x00\x01\x05\x87\x4b\xa1\xff" := by native_decide

-- ==============
-- =  Decoding  =
-- ==============

/-- Convert a String of codepoint-as-byte characters to its `ByteArray` representation.
    Test-only helper: matches the historical convention where each Char in 0–255 stands
    for the byte with the same value (the same convention used by the UPLC `ByteString`
    domain wrapper). -/
private def s2ba (s : String) : ByteArray := (Char.toUInt8 <$> s.data).toByteArray

example : d₈ ("deadbeef".data.map Char.toUInt8) = .some ([], 7234295460216005990) := by rfl
example : d₁ ("deadbeef".data.map Char.toUInt8) = .some ("eadbeef".data.map Char.toUInt8, 100) := by rfl

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

end PlutusCore.Cbor

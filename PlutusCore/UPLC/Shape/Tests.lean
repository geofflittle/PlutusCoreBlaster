import PlutusCore.UPLC.Shape.Basic

namespace PlutusCore.UPLC.Shape

open PlutusCore.UPLC.Shape.Internal

example : toString (.ConInteger : TermShape) = "Int"    := by decide +native
example : toString (.ConString  : TermShape) = "String" := by decide +native
example : toString (.Function .ConInteger (.Function .ConInteger .ConInteger) : TermShape)
                                             = "Int → Int → Int" := by decide +native
example : toString (.Delay .ConByteString : TermShape) = "Delay (ByteString)" := by decide +native
example : toString (.Function .ConBool (.Function (.TypeVar 0) (.Function (.TypeVar 0) (.TypeVar 0))) : TermShape)
                                             = "Bool → α → α → α" := by decide +native
example : toString (.Function (.Function .ConInteger .ConInteger) .ConBool : TermShape)
                                             = "(Int → Int) → Bool" := by decide +native
example : toString (.Alternatives [.ConInteger, .ConString, .ConByteString] : TermShape)
                                             = "Int | String | ByteString" := by decide +native

example : toString (VarTable.unify .empty
                     (.Function .Anything .ConBool)
                     (.Function .ConInteger .Anything)).fst
        = "Int → Bool" := by decide +native

example : toString (VarTable.unify .empty (.Delay .Anything) (.Delay .ConString)).fst
        = "Delay (String)" := by decide +native

example : toString (VarTable.unify .empty
                     (.Function .ConInteger .ConBool)
                     (.Function .ConString  .ConBool)).fst
        = "Nothing" := by decide +native

example : toString (VarTable.unify .empty
                     (.Alternatives [.ConInteger, .ConString, .ConByteString])
                     (.Alternatives [.ConString, .ConByteString, .ConBool])).fst
                  = "String | ByteString" := by decide +native

example : toString (VarTable.unify .empty
                     (.Alternatives [.Function .ConInteger .ConInteger, .Function .ConInteger .ConBool])
                     (.Function .ConInteger .ConBool)).fst
                  = "Int → Bool"       := by decide +native

example : toString (VarTable.unify .empty (.Alternatives [.ConInteger, .ConString]) .ConInteger).fst
                  = "Int"              := by decide +native
example : toString (VarTable.unify .empty .ConInteger (.Alternatives [.ConInteger, .ConString])).fst
                  = "Int"              := by decide +native
example : toString (VarTable.unify .empty (.Alternatives [.ConInteger, .ConString]) .ConBool).fst
                  = "Nothing"          := by decide +native

example : toString (unifyAlternatives [.ConInteger, .ConInteger])          = "Int"          := by decide +native
example : toString (unifyAlternatives [.ConInteger, .ConString])           = "Int | String" := by decide +native
example : toString (unifyAlternatives [.ConInteger, .Nothing])             = "Int"          := by decide +native
example : toString (unifyAlternatives [.ConInteger, .Anything])            = "Anything"     := by decide +native
example : toString (unifyAlternatives ([] : List TermShape))               = "Anything"     := by decide +native
example : toString (unifyAlternatives [.Alternatives [.ConInteger, .ConString], .ConByteString])
                                                                           = "Int | String | ByteString" := by decide +native

example : toString (analyzeType (.Const (.Integer 42)))
                  = "Int"             := by decide +native

example : toString (analyzeType (.Lam "x" (.Const (.Bool true))))
                  = "Anything → Bool" := by decide +native

example : toString (analyzeType (.Builtin .AddInteger))
                  = "Int → Int → Int" := by decide +native

example : toString (analyzeType (.Apply (.Builtin .AddInteger) (.Const (.Integer 42))))
                  = "Int → Int"       := by decide +native

example : toString (analyzeType (.Apply (.Builtin .AddInteger) (.Const (.String "42"))))
                  = "Nothing"         := by decide +native

example : toString (analyzeType (.Builtin .IfThenElse))
                  = "Delay (Bool → α → α → α)" := by decide +native

example : toString (analyzeType (.Force (.Builtin .IfThenElse)))
                  = "Bool → α → α → α" := by decide +native

example : toString (analyzeType (.Apply (.Force (.Builtin .IfThenElse)) (.Const .Unit)))
                  = "Nothing"          := by decide +native

example : toString (analyzeType (.Apply (.Force (.Builtin .IfThenElse)) (.Const (.Bool true))))
                  = "α → α → α"        := by decide +native

example : toString (analyzeType (.Lam "x" (.Apply (.Force (.Builtin .IfThenElse)) (.Var "x"))))
                  = "Bool → α → α → α" := by decide +native

example : toString (analyzeType (.Builtin .EqualsInteger))
                  = "Int → Int → Bool" := by decide +native

example : toString (analyzeType (.Force (.Builtin .HeadList)))
                  = "List → α"         := by decide +native

example : toString (analyzeType .Error)
                  = "Nothing"          := by decide +native

example : toString (analyzeType (.Case (.Const (.Bool true)) [.Const (.Integer 1), .Const (.Integer 2)]))
                  = "Int"              := by decide +native

example : toString (analyzeType (.Constr 0 [.Const (.Integer 1)]))
                  = "Anything"         := by decide +native

example : toString (analyzeType (.Case (.Const (.Bool true)) [.Const (.Integer 1), .Const (.String "a")]))
                  = "Int | String"     := by decide +native

end PlutusCore.UPLC.Shape

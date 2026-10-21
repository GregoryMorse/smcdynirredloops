module

public import SmcIrred.Paper

public section

/-!
# Proved solution

Proves `PalomarSIL.mathematical_result` of `Challenge.lean` from the verified development: every conjunct is a statement of
`SmcIrred.Spec.Paper` that `SmcIrred.Paper` derives from the theorems of the development (solver and planted generator,
extremal numbers, transformations, security model with its structural assumptions). The AES graphs are the separate
Challenge `ChallengeAES.lean` (one Challenge may have at most 1,000 lines).
-/

namespace PalomarSIL

theorem mathematical_result :
    SmcIrred.Paper.SmcTwoSatCorrect ∧ SmcIrred.Paper.IrreducibleExtremal ∧ SmcIrred.Paper.TransformCorrect ∧
      SmcIrred.Paper.SecurityModel :=
  ⟨SmcIrred.Paper.smcTwoSatCorrect, SmcIrred.Paper.irreducibleExtremal, SmcIrred.Paper.transformCorrect,
    SmcIrred.Paper.securityModel⟩

end PalomarSIL

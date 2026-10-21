module

public import SmcIrred.Paper

public section

/-!
# Proved solution (AES graphs)

Proves `PalomarSIL.mathematical_result` of `ChallengeAES.lean` from `SmcIrred.Paper.circuitCFGCorrect`.
-/

namespace PalomarSIL

theorem mathematical_result : SmcIrred.Paper.CircuitCFGCorrect := SmcIrred.Paper.circuitCFGCorrect

end PalomarSIL

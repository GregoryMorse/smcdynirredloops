module

public import SmcIrred.Spec.Paper
public import SmcIrred.Smc.Solve
public import SmcIrred.Tarjan.Solver
public import SmcIrred.Gen.Planted
public import SmcIrred.Gen.Construct
public import SmcIrred.Extremal.MinOther
public import SmcIrred.Extremal.MnCount
public import SmcIrred.Extremal.KnAny
public import SmcIrred.Lang.General
public import SmcIrred.Dynamic.StaticSchemeGeneral
public import SmcIrred.AES.KeyOK
public import SmcIrred.Threat.NotIO
public import SmcIrred.Threat.Necessity
public import SmcIrred.Threat.Recover
public import SmcIrred.Threat.Structuring
public import SmcIrred.Threat.DCA

public section

namespace SmcIrred.Paper

open SmcIrred.Lang SmcIrred.Dyn SmcIrred.Threat SmcIrred.Struct

/-- `SmcTwoSatCorrect`: `Smc.smcSolve_spec`, `twoSatSolve_spec`, `planted_smc`. -/
theorem smcTwoSatCorrect : SmcTwoSatCorrect :=
  ⟨fun f hw hne => smcSolve_spec f hw hne, fun f hw hne => twoSatSolve_spec f hw hne,
    fun _ _ _ _ _ hp hx hwx => planted_smc hp hx hwx,
    fun _ _ _ _ _ hs hc => ⟨genForest_planted hs hc, fun e he => ⟨genExtra_respects e he, genExtra_wf e he⟩,
      planted_smc (genForest_planted hs hc) (fun e he => genExtra_respects e he) (fun e he => genExtra_wf e he)⟩⟩

/-- `IrreducibleExtremal`: `irrCount_le`, `meeCount_le`, `Kn_irrCount`, `Mn_irrCount`, `maxMEE_others`, `MnLite_others`. -/
theorem irreducibleExtremal : IrreducibleExtremal :=
  ⟨fun _ _ _ hc hv hn => ⟨irrCount_le hc hv hn, meeCount_le hc hv⟩,
    fun n hn => ⟨Kn_valid (by omega), Kn_irrCount hn, Kn_meeCount n⟩,
    fun n hn => ⟨Mn_valid (by omega), Mn_irrCount hn, Mn_meeCount n⟩,
    fun _ _ _ hc hv hn hmax => maxMEE_others hc hv hn hmax,
    fun n hn => ⟨MnLite_valid (by omega), by rw [MnLite_meeCount_eq]; exact Kn_meeCount n, MnLite_others hn⟩⟩

/-- `TransformCorrect`: `path_one_edge_reducible_all`, `nway_one_edge_all`, `static_scheme_general`, `static_scheme_general6`. -/
theorem transformCorrect : TransformCorrect :=
  ⟨fun n => path_one_edge_reducible_all n, fun k hk => nway_one_edge_all k hk,
    fun _ _ _ _ _ hp hx hwx h1 h2 hr1 hr2 hs1 hs2 _ _ hS hT hS1 =>
      static_scheme_general hp hx hwx h1 h2 hr1 hr2 hs1 hs2 hS hT hS1,
    fun _ _ _ _ _ hp hx hwx h1 hr1 hs1 _ _ hS hT hS1 cd => static_scheme_general6 hp hx hwx h1 hr1 hs1 hS hT hS1 cd⟩

/-- `CircuitCFGCorrect`: `aes128Graph_correct`, `aes192Graph_correct`, `aes256Graph_correct`. -/
theorem circuitCFGCorrect : CircuitCFGCorrect :=
  ⟨fun key inp hinp => (aes128Graph_correct key inp hinp).2.2, fun key inp hinp => (aes192Graph_correct key inp hinp).2.2,
    fun key inp hinp => (aes256Graph_correct key inp hinp).2.2⟩

/-- `SecurityModel`: T1 `correct`, T2 `imm_unsound`, T3 `recover`, T4 `Kn_meeCount`, `one_variable_suffices`, T5 `fault_class`,
`fault_final_overwrites`, T6 `dca_final_obs`, T7 `not_size_indist`, and the necessity witnesses `nec_stamped`, `nec_forcing`,
`nec_false_cells`, `nec_extra_respects`, `nec_schedule`, `nec_topo`. -/
theorem securityModel : SecurityModel :=
  ⟨fun _ hA ho => correct hA ho, fun ho _ hC => imm_unsound ho hC, fun hC _ hA => recover hC hA, fun n => Kn_meeCount n,
    fun g hwf lab ch => one_variable_suffices g hwf lab ch,
    fun c hT _ _ _ hord hx δ σ τ => fault_class c hT hord hx δ σ τ,
    fun c _ _ _ hx δ σ => fault_final_overwrites c hx δ σ,
    fun c hT _ _ ha hb σ σ' => dca_final_obs c hT ha hb σ σ',
    fun O hlo hhi => not_size_indist O hlo hhi,
    ⟨dStamp, nec_stamped⟩, ⟨dForce, nec_forcing⟩, ⟨dFalse, nec_false_cells⟩, ⟨dExtra, nec_extra_respects⟩,
    ⟨wcirc, wcirc_topo, execs [1, 0], wcirc_bad_not_ordered, 1, wcirc_bad_order⟩, ⟨ccirc, nec_topo⟩,
    ⟨ncirc, ncirc_not_topo, execs [1, 0], ncirc_ordered, 0, by decide, ncirc_bad⟩⟩

end SmcIrred.Paper

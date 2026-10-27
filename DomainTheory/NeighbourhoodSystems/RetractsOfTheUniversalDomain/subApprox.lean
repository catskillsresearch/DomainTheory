module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.sub
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition_6_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_13
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_24

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`sub`, transported to the function space's own `Element` type via `funSpaceEquiv`.** -/
def subFilter (φ : (funSpace E E).Element) : (funSpace E E).Element :=
  toFilter (sub (toApproxMap φ))

theorem toApproxMap_monotone {φ ψ : (funSpace E E).Element} (h : φ ≤ ψ) :
    toApproxMap φ ≤ toApproxMap ψ := by
  have := (funSpaceEquiv E E).monotone h
  simpa using this

theorem subFilter_mono {φ ψ : (funSpace E E).Element} (h : φ ≤ ψ) : subFilter φ ≤ subFilter ψ :=
  toFilter_le_iff.mpr (sub.mono (toApproxMap_monotone h))

theorem subFilter_monotone : Monotone (subFilter (E := E)) := fun _ _ h => subFilter_mono h

/-- Directed unions of filters correspond, under `toApproxMap`, to the raw (pointwise) union of the
underlying maps' relations — immediate from `mem_iSupDirected` unfolded through `toApproxMap_rel`.
No consistency/directedness argument is needed for this direction. -/
theorem toApproxMap_rel_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k) {X Z : Set α} :
    (toApproxMap (iSupDirected φ hdir)).rel X Z ↔ ∃ i, (toApproxMap (φ i)).rel X Z := by
  simp only [toApproxMap_rel, mem_iSupDirected]

/-- **`sub` commutes with directed unions of relations.** `sub`'s formula (`sub.rel`) is a positive
existential in `f`'s relation (`∃Y, ... ∧ f.rel Y Y ∧ ...`), so it commutes with an arbitrary union
of relations by pure logic (swapping the order of two existentials) — no directedness needed here
either, only for `iSupDirected` to be well-formed in the first place. -/
theorem sub_toApproxMap_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k) {X Z : Set α} :
    (sub (toApproxMap (iSupDirected φ hdir))).rel X Z ↔
      ∃ i, (sub (toApproxMap (φ i))).rel X Z := by
  simp only [sub.rel, toApproxMap_rel_iSupDirected]
  constructor
  · rintro ⟨hX, hZ, Y, ⟨hYE, i, hYi⟩, hXY, hYZ⟩
    exact ⟨i, hX, hZ, Y, ⟨hYE, hYi⟩, hXY, hYZ⟩
  · rintro ⟨i, hX, hZ, Y, ⟨hYE, hYi⟩, hXY, hYZ⟩
    exact ⟨hX, hZ, Y, ⟨hYE, i, hYi⟩, hXY, hYZ⟩

theorem toApproxMap_toFilter (f : ApproximableMap E E) : toApproxMap (toFilter f) = f :=
  (funSpaceEquiv E E).right_inv f

theorem toApproxMap_subFilter (φ : (funSpace E E).Element) :
    toApproxMap (subFilter φ) = sub (toApproxMap φ) :=
  toApproxMap_toFilter _

theorem toFilter_toApproxMap (φ : (funSpace E E).Element) : toFilter (toApproxMap φ) = φ :=
  (funSpaceEquiv E E).left_inv φ

theorem toApproxMap_injective {φ ψ : (funSpace E E).Element} (h : toApproxMap φ = toApproxMap ψ) :
    φ = ψ := by
  rw [← toFilter_toApproxMap φ, ← toFilter_toApproxMap ψ, h]

/-- **`subFilter` preserves directed unions.** Assembled from `sub_toApproxMap_iSupDirected` and
`toApproxMap_rel_iSupDirected` via `toApproxMap`'s injectivity. -/
theorem subFilter_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k)
    (hdir' : ∀ i j, ∃ k, subFilter (φ i) ≤ subFilter (φ k) ∧ subFilter (φ j) ≤ subFilter (φ k)) :
    subFilter (iSupDirected φ hdir) = iSupDirected (fun i => subFilter (φ i)) hdir' := by
  apply toApproxMap_injective
  rw [toApproxMap_subFilter]
  apply ApproximableMap.ext
  intro X Z
  rw [sub_toApproxMap_iSupDirected, toApproxMap_rel_iSupDirected]
  simp only [toApproxMap_subFilter]

/-- **`subFilter` is (topologically) continuous**, via the domain-theoretic bridge
`continuous_of_monotone_iSupDirected` (monotone + preserves directed unions). -/
theorem continuous_subFilter : Continuous (subFilter (E := E)) :=
  continuous_of_monotone_iSupDirected subFilter_monotone subFilter_iSupDirected

end Sub8_6

/-- **`sub`, packaged as a genuine approximable map on the function space `(E → E)`** (Scott's
remark that `f ↦ sub(f)` is itself approximable), via Exercise 2.13's `ofContinuous`. -/
def subApprox : ApproximableMap (funSpace E E) (funSpace E E) :=
  ofContinuous Sub8_6.subFilter Sub8_6.continuous_subFilter

namespace subApprox

/-- Unfolds `ofContinuous` at the element level. -/
theorem toElementMap_eq (φ : (funSpace E E).Element) :
    ApproximableMap.toElementMap subApprox φ = Sub8_6.subFilter φ :=
  toElementMap_ofContinuous Sub8_6.subFilter Sub8_6.continuous_subFilter φ

/-- **`Fix(subApprox) ≃o {f ∣ sub f = f}`.** `subApprox.toElementMap φ = φ` unfolds (via
`toElementMap_eq`/`subFilter`) to `toFilter (sub (toApproxMap φ)) = φ`, i.e. exactly
`sub (toApproxMap φ) = toApproxMap φ` after transporting through `toApproxMap`/`toFilter`'s round
trips. -/
def fixIso :
    {φ : (funSpace E E).Element // ApproximableMap.toElementMap subApprox φ = φ} ≃o
      {f : ApproximableMap E E // sub f = f} where
  toFun φ := ⟨toApproxMap φ.1, by
    have h1 : Sub8_6.subFilter φ.1 = φ.1 := (toElementMap_eq φ.1).symm.trans φ.2
    have h2 : toApproxMap (Sub8_6.subFilter φ.1) = toApproxMap φ.1 := congrArg toApproxMap h1
    rwa [Sub8_6.toApproxMap_subFilter] at h2⟩
  invFun f := ⟨toFilter f.1, by
    rw [toElementMap_eq]
    show Sub8_6.subFilter (toFilter f.1) = toFilter f.1
    unfold Sub8_6.subFilter
    rw [Sub8_6.toApproxMap_toFilter, f.2]⟩
  left_inv φ := Subtype.ext (Sub8_6.toFilter_toApproxMap φ.1)
  right_inv f := Subtype.ext (Sub8_6.toApproxMap_toFilter f.1)
  map_rel_iff' := by
    intro φ ψ
    show toApproxMap φ.1 ≤ toApproxMap ψ.1 ↔ φ.1 ≤ ψ.1
    exact (funSpaceEquiv E E).map_rel_iff

/-- **Theorem 8.6(b)(ii) (Scott 1981, PRG-19).** `subApprox` is finitary: composing
`fixIso` with `finitaryProjectionSubsystemEquiv` and Proposition 6.11's
`subsystemReprIso` witnesses `Fix(subApprox)` as (order-isomorphic to) a genuine domain. -/
theorem isFinitary : IsFinitary (subApprox (E := E)) :=
  ⟨_, _, ⟨fixIso.trans
    ((finitaryProjectionSubsystemEquiv E).trans (Proposition611.subsystemReprIso E))⟩⟩

end subApprox

namespace Sub8_6


/-- **`subApprox` is a projection**: `subApprox ≤ idMap`, from `subFilter φ ≤ φ`, itself
inherited from `sub_le`. -/
theorem subApprox_le_idMap : subApprox ≤ idMap (funSpace E E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [subApprox.toElementMap_eq, toElementMap_idMap]
  calc subFilter φ = toFilter (sub (toApproxMap φ)) := rfl
    _ ≤ toFilter (toApproxMap φ) := toFilter_le_iff.mpr (sub_le _)
    _ = φ := toFilter_toApproxMap φ

end Sub8_6

namespace Sub8_6


theorem subFilter_subFilter (φ : (funSpace E E).Element) :
    subFilter (subFilter φ) = subFilter φ := by
  unfold subFilter
  rw [toApproxMap_toFilter, sub_sub]

theorem subApprox.toElementMap_eq_comp (φ : (funSpace E E).Element) :
    (subApprox.comp subApprox).toElementMap φ = subApprox.toElementMap φ := by
  rw [toElementMap_comp]
  simp only [subApprox.toElementMap_eq]
  exact subFilter_subFilter φ

/-- **`subApprox` is a retraction**: `subApprox ∘ subApprox = subApprox`, from `subFilter`'s own
idempotency (`subFilter_subFilter`), itself inherited from `sub_sub`. Proved via `le_antisymm` on
`le_iff_toElementMap_le` (choice-free), rather than the classical `ext_of_toElementMap`. -/
theorem isRetraction_subApprox : Retraction (subApprox (E := E)) :=
  ⟨le_antisymm (le_iff_toElementMap_le.mpr fun φ => (subApprox.toElementMap_eq_comp φ).le)
    (le_iff_toElementMap_le.mpr fun φ => (subApprox.toElementMap_eq_comp φ).ge)⟩

/-- **`sub` is itself a *projection* on the function space `(E → E)`** (half of Theorem 8.6's
second clause; the other half, `IsFinitary subApprox`, is below). -/
theorem isProjection_subApprox : IsProjection (subApprox (E := E)) :=
  ⟨isRetraction_subApprox, subApprox_le_idMap⟩

/-- **Theorem 8.6(b), in full.** `subApprox` is a finitary projection on `(E → E)`. -/
theorem isFinitaryProjection_subApprox : FinitaryProjection (subApprox (E := E)) :=
  ⟨⟨isProjection_subApprox, subApprox.isFinitary⟩⟩

end Sub8_6

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6
variable {α : Type*} {E : NeighborhoodSystem α}

/-- **`subApprox`'s relation, unfolded via `ofMono`/`ofContinuous`/`toFilter`.** `F subApprox G`
holds iff `G` is a genuine function-space neighbourhood containing `sub` of `F`'s least map (any
witnessing proof `hF` of `F`'s membership works, by proof irrelevance). -/
theorem subApprox_rel_iff {F G : Set (ApproximableMap E E)} (hF : (funSpace E E).mem F) :
    (subApprox (E := E)).rel F G ↔
      (funSpace E E).mem G ∧ sub (toApproxMap ((funSpace E E).principal hF)) ∈ G :=
  ⟨fun ⟨_, hG, hmem⟩ => ⟨hG, hmem⟩, fun ⟨hG, hmem⟩ => ⟨hF, hG, hmem⟩⟩

section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)

/-- **`subApprox`'s relation, specialized to `Xenum`.** `(Xenum n) subApprox (Xenum m)` holds iff,
whenever `m` is consistent, `sub` of `Xenum n`'s least map relates every coded step of `Xenum m`. -/
theorem subApprox_rel_Xenum_iff (n m : ℕ) :
    (subApprox (E := E)).rel (Xenum P P gN n) (Xenum P P gN m) ↔
      gN m = 1 → ∀ e ∈ decodeList m,
        (sub (toApproxMap ((funSpace E E).principal (Xenum_mem P P gN hgN n)))).rel
          (P.X e.unpair.1) (P.X e.unpair.2) := by
  rw [subApprox_rel_iff (Xenum_mem P P gN hgN n), and_iff_right (Xenum_mem P P gN hgN m)]
  exact mem_Xenum_iff_map P P gN _ m

/-- **The per-witness `sub`-step predicate is recursively decidable**, coded as a function of
`w = ⟨y, ⟨n, e⟩⟩`: the function-space inclusion `Xenum n ⊆ Xenum (codePair y y)` (via `fincl`, the
function-space presentation's own inclusion char) conjoined with the two `𝒟`-inclusions bracketing
`y` (via `incl`, `P`'s own inclusion char). -/
theorem subStep_recDecidable (fincl incl : ℕ → ℕ)
    (hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2)
    (hfinclp : Nat.Primrec fincl)
    (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl) :
    RecDecidable (fun w : ℕ =>
      Xenum P P gN w.unpair.2.unpair.1 ⊆ Xenum P P gN (codePair w.unpair.1 w.unpair.1) ∧
        P.X w.unpair.2.unpair.2.unpair.1 ⊆ P.X w.unpair.1 ∧
          P.X w.unpair.1 ⊆ P.X w.unpair.2.unpair.2.unpair.2) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he1 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hcodeYY : Nat.Primrec (fun w : ℕ => codePair w.unpair.1 w.unpair.1) :=
    Nat.Primrec.succ.comp ((hy.pair hy).pair (Nat.Primrec.const 0))
  have h1 : RecDecidable (fun w : ℕ =>
      Xenum P P gN w.unpair.2.unpair.1 ⊆ Xenum P P gN (codePair w.unpair.1 w.unpair.1)) :=
    ⟨fun w => fincl (Nat.pair w.unpair.2.unpair.1 (codePair w.unpair.1 w.unpair.1)),
      hfinclp.comp (hn.pair hcodeYY), fun w => by
        rw [hfincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  have h2 : RecDecidable (fun w : ℕ => P.X w.unpair.2.unpair.2.unpair.1 ⊆ P.X w.unpair.1) :=
    ⟨fun w => incl (Nat.pair w.unpair.2.unpair.2.unpair.1 w.unpair.1), hinclp.comp (he1.pair hy),
      fun w => by rw [hincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  have h3 : RecDecidable (fun w : ℕ => P.X w.unpair.1 ⊆ P.X w.unpair.2.unpair.2.unpair.2) :=
    ⟨fun w => incl (Nat.pair w.unpair.1 w.unpair.2.unpair.2.unpair.2), hinclp.comp (hy.pair he2),
      fun w => by rw [hincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  exact h1.and (h2.and h3)

/-- **`sub`'s defining existential, reindexed to presentation indices.** `sub f` relates presented
neighbourhoods `X_a`, `X_b` iff some presented `X_y` witnesses Scott's formula (`P.surj` turns the
arbitrary witness neighbourhood `Y` of `sub.rel` into an index `y`). -/
theorem sub_rel_iff_exists_index {f : ApproximableMap E E} {a b : ℕ} :
    (sub f).rel (P.X a) (P.X b) ↔
      ∃ y : ℕ, f.rel (P.X y) (P.X y) ∧ P.X a ⊆ P.X y ∧ P.X y ⊆ P.X b := by
  rw [sub.rel, and_iff_right (P.mem_X a), and_iff_right (P.mem_X b)]
  constructor
  · rintro ⟨Y, ⟨hYE, hYf⟩, haY, hYb⟩
    obtain ⟨y, rfl⟩ := P.surj hYE
    exact ⟨y, hYf, haY, hYb⟩
  · rintro ⟨y, hYf, haY, hYb⟩
    exact ⟨P.X y, ⟨P.mem_X y, hYf⟩, haY, hYb⟩

/-- **`sub` of `Xenum n`'s least map, in fully decidable-existential form.** Combines
`sub_rel_iff_exists_index` with Theorem 7.6's `leastMap_Xenum_rel`/`Xenum_codePair` to turn the
witness condition `ĝₙ.rel (X_y) (X_y)` into the recursively decidable function-space inclusion
`Xenum n ⊆ Xenum (codePair y y)`. -/
theorem sub_leastMap_rel_iff (n a b : ℕ) :
    (sub (toApproxMap ((funSpace E E).principal (Xenum_mem P P gN hgN n)))).rel
        (P.X a) (P.X b) ↔
      ∃ y : ℕ, Xenum P P gN n ⊆ Xenum P P gN (codePair y y) ∧
        P.X a ⊆ P.X y ∧ P.X y ⊆ P.X b := by
  rw [sub_rel_iff_exists_index P]
  refine exists_congr (fun y => ?_)
  rw [leastMap_Xenum_rel P gN hgN n y y, Xenum_codePair P gN hgN y y]

/-- **Theorem 8.6(c) (Scott 1981, PRG-19), as an `ComputableMap` statement.** Relative to the
function-space presentation `funPresentation P P …` (Theorem 7.5) built from any presentation `P` of
`E`, `subApprox` is computable: its neighbourhood relation is the recursively enumerable
`¬(consistent m) ∨ ∀ e ∈ decodeList m, ∃ y, …` (a bounded `∀` of an unbounded `∃` of a decidable
predicate). -/
theorem subApprox_isComputable
    (incl eq : ℕ → ℕ)
    (hgNp : Nat.Primrec gN)
    (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl)
    (heq : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2) (heqp : Nat.Primrec eq) :
    ComputableMap
      (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp)
      (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp)
      (subApprox (E := E)) := by
  constructor
  obtain ⟨fincl, hfinclp, hfincls⟩ :=
    (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp).incl_computable
  have hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2 :=
    fun s => (hfincls s).symm
  show REPred₂ (fun n m => (subApprox (E := E)).rel (Xenum P P gN n) (Xenum P P gN m))
  have hdec := subStep_recDecidable P gN fincl incl hfincl hfinclp hincl hinclp
  have hre : REPred₂ (fun n e => ∃ y : ℕ,
      Xenum P P gN n ⊆ Xenum P P gN (codePair y y) ∧
        P.X e.unpair.1 ⊆ P.X y ∧ P.X y ⊆ P.X e.unpair.2) := by
    refine REPred.of_iff (fun t => ?_) hdec.re.proj
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hforall : REPred (fun t => ∀ e ∈ decodeList t.unpair.2, ∃ y : ℕ,
      Xenum P P gN t.unpair.1 ⊆ Xenum P P gN (codePair y y) ∧
        P.X e.unpair.1 ⊆ P.X y ∧ P.X y ⊆ P.X e.unpair.2) :=
    REPred.forall_mem_decodeList₂ hre
  have hne1 : REPred (fun t => ¬ gN t.unpair.2 = 1) :=
    ((RecDecidable.natEq (hgNp.comp Nat.Primrec.right) (Nat.Primrec.const 1)).not).re
  refine REPred.of_iff (fun t => ?_) (hne1.or hforall)
  show (subApprox (E := E)).rel (Xenum P P gN t.unpair.1) (Xenum P P gN t.unpair.2) ↔ _
  rw [subApprox_rel_Xenum_iff P gN hgN t.unpair.1 t.unpair.2, Decidable.imp_iff_not_or]
  refine or_congr_right (forall_congr' (fun e => imp_congr_right (fun _ => ?_)))
  exact sub_leastMap_rel_iff P gN hgN t.unpair.1 e.unpair.1 e.unpair.2

end SubComputable

/-- **Theorem 8.6(c) (Scott 1981, PRG-19), in full: "If `E` is effectively given, then `sub` is
computable."** Packages `subApprox_isComputable` with the function-space presentation that Theorem
7.5 (`funSpace_isEffectivelyGiven`'s construction, `funPresentation`) builds out of any computable
presentation of `E`. -/
theorem sub_isComputable_of_isEffectivelyGiven (h : E.IsEffectivelyGiven) :
    ∃ Pfun : ComputablePresentation (funSpace E E),
      ComputableMap Pfun Pfun (subApprox (E := E)) := by
  obtain ⟨P⟩ := h
  obtain ⟨incl, hinclp, hincls⟩ := P.incl_computable
  obtain ⟨eq, heqp, heqs⟩ := P.eq_computable
  obtain ⟨fc, hfcp, hfcs⟩ := P.cons_computable
  have hincl' : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2 := fun s => (hincls s).symm
  have heq' : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2 := fun s => (heqs s).symm
  have hgN : ∀ c, funConsChar P P fc fc c = 1 ↔
      (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty :=
    fun c => funConsChar_spec P P fc fc (fun s => (hfcs s).symm) (fun s => (hfcs s).symm) c
  refine ⟨funPresentation P P (funConsChar P P fc fc) incl incl eq hgN
    (primrec_funConsChar P P fc fc hfcp hfcp) hincl' hinclp hincl' hinclp heq' heqp,
    subApprox_isComputable P (funConsChar P P fc fc) hgN incl eq
      (primrec_funConsChar P P fc fc hfcp hfcp) hincl' hinclp heq' heqp⟩

end

end DomainTheory.NeighbourhoodSystems

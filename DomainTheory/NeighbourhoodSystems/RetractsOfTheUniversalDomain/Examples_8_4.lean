module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_10
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_3
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.smashRetraction

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap ApproximableMap₂

/- concordance: source L4807 EXAMPLES 8.4 strict / fixedNbhd -/

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

/-- `g(f, y) = fade(check(y), f(y))`, as a joint approximable map `(D → E) × D → E`. -/
def strictEvalFade : ApproximableMap (prod (funSpace D E) D) E :=
  (fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))

end Strict

section Strict

/-- **Example 8.4(b)(i)'s `strict` combinator.** `strict(f) = λy. fade(check(y), f(y))`, built via
Theorem 3.12's `curry`. -/
def strictRetraction : ApproximableMap (funSpace D E) (funSpace D E) := curry strictEvalFade

end Strict

section Strict

/-- The closed form of `strict`'s elementwise action: `strict(f)(y) = ⊥_E` if `y = ⊥_D`, else
`f(y)`. -/
theorem toApproxMap_strictRetraction_mem {φ : (funSpace D E).Element} {y : D.Element}
    {Z : Set β} :
    ((toApproxMap (strictRetraction.toElementMap φ)).toElementMap y).mem Z ↔
      E.mem Z ∧ (Z = E.master ∨ (y ≠ D.bot ∧ ((toApproxMap φ).toElementMap y).mem Z)) := by
  show ((toApproxMap ((curry strictEvalFade).toElementMap φ)).toElementMap y).mem Z ↔ _
  rw [toElementMap_curry_apply]
  show (((fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))).toElementMap
      (pair φ y)).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₁, snd_pair,
    evalMap_apply, mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

end Strict

section Strict

theorem strictRetraction_apply_bot (φ : (funSpace D E).Element) :
    (toApproxMap (strictRetraction.toElementMap φ)).toElementMap D.bot = E.bot := by
  apply Element.ext
  intro Z
  rw [toApproxMap_strictRetraction_mem, mem_bot]
  constructor
  · rintro ⟨-, rfl | ⟨hne, -⟩⟩
    · rfl
    · exact absurd rfl hne
  · rintro rfl
    exact ⟨E.master_mem, Or.inl rfl⟩

end Strict

section Strict

/-- **`f` is a fixed point of `strict` iff `f` is strict.** -/
theorem isStrict_toApproxMap_of_fixed {φ : (funSpace D E).Element}
    (hφ : strictRetraction.toElementMap φ = φ) : Exercise510.IsStrict (toApproxMap φ) := by
  rw [Exercise510.isStrict_iff_apply_bot]
  have h := strictRetraction_apply_bot φ
  rwa [hφ] at h

end Strict

section Strict

theorem strictRetraction_apply_of_ne_bot {y : D.Element} (hy : y ≠ D.bot)
    (φ : (funSpace D E).Element) :
    (toApproxMap (strictRetraction.toElementMap φ)).toElementMap y
      = (toApproxMap φ).toElementMap y := by
  apply Element.ext
  intro Z
  rw [toApproxMap_strictRetraction_mem]
  constructor
  · rintro ⟨-, rfl | ⟨-, hZ⟩⟩
    · exact ((toApproxMap φ).toElementMap y).master_mem
    · exact hZ
  · intro hZ
    exact ⟨((toApproxMap φ).toElementMap y).sub hZ, Or.inr ⟨hy, hZ⟩⟩

end Strict

section Strict

theorem toApproxMap_toFilter (f : ApproximableMap D E) : toApproxMap (toFilter f) = f :=
  (funSpaceEquiv D E).right_inv f

end Strict

section Strict

/-- Two tiny reproofs of `funSpaceEquiv`'s own round-trips, stated standalone so the closed-form
calculations below don't have to fight `OrderIso` field-access notation. -/
theorem toFilter_toApproxMap (φ : (funSpace D E).Element) : toFilter (toApproxMap φ) = φ :=
  (funSpaceEquiv D E).left_inv φ

end Strict

section Strict

theorem strictRetraction_fixed_of_isStrict {f : ApproximableMap D E} (hf : Exercise510.IsStrict f) :
    strictRetraction.toElementMap (toFilter f) = toFilter f := by
  have hbot : f.toElementMap D.bot = E.bot := Exercise510.isStrict_iff_apply_bot.mp hf
  have key : toApproxMap (strictRetraction.toElementMap (toFilter f)) = f := by
    apply ext_of_toElementMap
    intro y
    by_cases hy : y = D.bot
    · rw [hy, strictRetraction_apply_bot, hbot]
    · rw [strictRetraction_apply_of_ne_bot hy, toApproxMap_toFilter]
  rw [← toFilter_toApproxMap (strictRetraction.toElementMap (toFilter f)), key]

end Strict

section Strict

/-- **Example 8.4(b)(i), the fixed-point representation.** Restricting `funSpaceEquiv` along
`isStrict_toApproxMap_of_fixed`/`strictRetraction_fixed_of_isStrict` identifies `Fix(strict)` with
the strict approximable maps `Exercise510.StrictMap D E`. -/
def strictRetractionFixIso :
    {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ} ≃o
      Exercise510.StrictMap D E where
  toFun φ := ⟨toApproxMap φ.1, isStrict_toApproxMap_of_fixed φ.2⟩
  invFun f := ⟨toFilter f.1, strictRetraction_fixed_of_isStrict f.2⟩
  left_inv φ := Subtype.ext (toFilter_toApproxMap φ.1)
  right_inv f := Subtype.ext (toApproxMap_toFilter f.1)
  map_rel_iff' := by
    intro φ φ'
    show toApproxMap φ.1 ≤ toApproxMap φ'.1 ↔ φ.1 ≤ φ'.1
    exact (funSpaceEquiv D E).map_rel_iff

end Strict

section Strict

theorem strictRetraction_le_idMap : strictRetraction (D := D) (E := E) ≤ idMap (funSpace D E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_idMap]
  have hmap : toApproxMap (strictRetraction.toElementMap φ) ≤ toApproxMap φ := by
    rw [le_iff_toElementMap_le]
    intro y
    by_cases hy : y = D.bot
    · rw [hy, strictRetraction_apply_bot]
      intro Z hZ
      rw [mem_bot] at hZ
      rw [hZ]
      exact ((toApproxMap φ).toElementMap D.bot).master_mem
    · rw [strictRetraction_apply_of_ne_bot hy]
  exact (funSpaceEquiv D E).map_rel_iff.mp hmap

end Strict

section Strict

theorem toApproxMap_injective {a b : (funSpace D E).Element} (h : toApproxMap a = toApproxMap b) :
    a = b := by
  rw [← toFilter_toApproxMap a, ← toFilter_toApproxMap b, h]

end Strict

section Strict

theorem isRetraction_strictRetraction : Retraction (strictRetraction (D := D) (E := E)) := by
  constructor
  apply ext_of_toElementMap
  intro φ
  rw [toElementMap_comp]
  apply toApproxMap_injective
  apply ext_of_toElementMap
  intro y
  by_cases hy : y = D.bot
  · rw [hy, strictRetraction_apply_bot, strictRetraction_apply_bot]
  · rw [strictRetraction_apply_of_ne_bot hy, strictRetraction_apply_of_ne_bot hy]

end Strict

section Strict

/-- **Example 8.4(b)(i) (Scott 1981, PRG-19).** `strictRetraction` is a projection on `D → E`
whose fixed-point set is isomorphic to the strict function space `Exercise510.strictFun D E`. -/
theorem example84b_strict :
    IsProjection (strictRetraction (D := D) (E := E)) ∧
      Nonempty ((Exercise510.strictFun D E).Element ≃o
        {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ}) :=
  ⟨⟨isRetraction_strictRetraction, strictRetraction_le_idMap⟩,
    ⟨strictRetractionFixIso.trans (Exercise510.strictFunEquiv D E).symm |>.symm⟩⟩

end Strict

end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- The fixed-point set of `a`, as a bare type — matching `IsFinitary`'s witness type. -/
abbrev FixSet (a : ApproximableMap E E) := {y : E.Element // a.toElementMap y = y}

/-- **The candidate subdomain of Theorem 8.5's proof, `D = {X ∈ E ∣ X a X}`.** Built for *any*
approximable map `a : E → E` — the neighbourhood-system axioms need only `mono`/`inter_right` of
`a`, no projection or finitary hypothesis. (This is also exactly Theorem 8.6's `Fix(sub)` predicate
`X sub(f) X`, restated for a single map `a` in place of the function-space token `f`.) -/
def fixedNbhd (a : ApproximableMap E E) : NeighborhoodSystem α where
  mem X := E.mem X ∧ a.rel X X
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := ⟨E.master_mem, a.master_rel⟩
  inter_mem := by
    rintro X Y Z ⟨hXE, hXa⟩ ⟨hYE, hYa⟩ ⟨hZE, _⟩ hZsub
    have hXYE : E.mem (X ∩ Y) := E.inter_mem hXE hYE hZE hZsub
    have h1 : a.rel (X ∩ Y) X :=
      a.mono hXa Set.inter_subset_left subset_rfl hXYE hXE
    have h2 : a.rel (X ∩ Y) Y :=
      a.mono hYa Set.inter_subset_right subset_rfl hXYE hYE
    exact ⟨hXYE, a.inter_right h1 h2⟩
  sub_master := fun h => E.sub_master h.1

@[simp] theorem fixedNbhd_mem {a : ApproximableMap E E} {X : Set α} :
    (fixedNbhd a).mem X ↔ E.mem X ∧ a.rel X X := Iff.rfl

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}

instance instNonemptyMemSubtype (x : V.Element) : Nonempty {X : Set γ // x.mem X} :=
  ⟨⟨V.master, x.master_mem⟩⟩

/-- **Compactness, as a standalone predicate**: `x` is compact iff every time `x` sits below a
directed union it already sits below one of the summands. By algebraicity, this is exactly the
same thing as being principal (`eq_principal_of_isCompactElt`). Stated with `I` fixed to `V`'s own
token universe (the only instantiation ever needed below), to sidestep spurious universe-metavariable
friction from a separately-auto-bound `Type*` inside a reusable `def`. -/
def IsCompactElt (x : V.Element) : Prop :=
  ∀ {I : Type u} [Nonempty I] (d : I → V.Element) (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k),
    x ≤ iSupDirected d hdir → ∃ i, x ≤ d i

end Algebraic

section HardDirection

variable {a : ApproximableMap E E}

variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)

/-- **The section `i : F → E`** induced by the abstract witness `e` of `IsFinitary a`: on the
principal element `↑X` of `F`, `i` returns the underlying `E`-element of `e.symm(↑X) ∈ Fix(a)`.
Built via `ofMono` (Exercise 2.8) — monotone on principals is all that's needed. -/
def sectionMap : ApproximableMap F E :=
  ofMono (fun _X hX => (e.symm (F.principal hX)).1) (fun _ _ hX hX' hXX' =>
    e.symm.monotone ((F.principal_le_iff hX hX').mpr hXX'))

end HardDirection

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}

/-- A neighbourhood `Z` witnessing `y`'s membership is always a *lower bound* on `y`: `↑Z ⊑ y`.
The general form of `Basic.lean`'s remark that `⊥ = ↑Δ` is least: any witnessed `↑Z` sits below
the element it witnesses. -/
theorem principal_le_of_mem {y : V.Element} {Z : Set γ} (hZ : y.mem Z) :
    V.principal (y.sub hZ) ≤ y :=
  fun _ ⟨hW, hZW⟩ => y.up_mem hZ hW hZW

theorem principalFamily_directed (x : V.Element) :
    ∀ i j : {X : Set γ // x.mem X}, ∃ k : {X : Set γ // x.mem X},
      V.principal (x.sub i.2) ≤ V.principal (x.sub k.2) ∧
        V.principal (x.sub j.2) ≤ V.principal (x.sub k.2) :=
  fun i j => ⟨⟨i.1 ∩ j.1, x.inter_mem i.2 j.2⟩,
    (V.principal_le_iff (x.sub i.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_left,
    (V.principal_le_iff (x.sub j.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_right⟩

/-- **Algebraicity.** Every element `x` is the directed union of its own principal
("finite"/compact) approximants: `x = ⋃ {↑X ∣ X ∈ x}`, now literally as an `iSupDirected`
(rather than `eq_iUnion_principal`'s membership-only form). -/
theorem eq_iSupDirected_principal (x : V.Element) :
    x = iSupDirected (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2))
      (principalFamily_directed x) := by
  apply Element.ext
  intro Z
  rw [mem_iSupDirected]
  constructor
  · intro hZ; exact ⟨⟨Z, hZ⟩, (V.mem_principal _).mpr ⟨x.sub hZ, subset_rfl⟩⟩
  · rintro ⟨⟨X, hX⟩, hZ'⟩
    obtain ⟨hZmem, hXZ⟩ := (V.mem_principal _).mp hZ'
    exact x.up_mem hX hZmem hXZ

end Algebraic

section HardDirection

variable {a : ApproximableMap E E}

/-- The sup of a directed family of `a`-fixed elements is again `a`-fixed: `a` is continuous
(`toElementMap_iSupDirected`), so `a` applied to the sup is the sup of `a` applied pointwise, which
is the original family by `hfix`. -/
theorem toElementMap_iSupDirected_fixed {I : Type u} [Nonempty I] (d : I → E.Element)
    (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k) (hfix : ∀ i, a.toElementMap (d i) = d i) :
    a.toElementMap (iSupDirected d hdir) = iSupDirected d hdir := by
  rw [toElementMap_iSupDirected]
  apply Element.ext
  intro Z
  rw [mem_iSupDirected, mem_iSupDirected]
  simp_rw [hfix]

variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)

@[simp] theorem toElementMap_sectionMap_principal {X : Set β} (hX : F.mem X) :
    (sectionMap e).toElementMap (F.principal hX) = (e.symm (F.principal hX)).1 :=
  toElementMap_ofMono_principal _ _ X hX

/-- **Claim′.** `i` realizes `e.symm` at *every* element of `F`, not just the principal ones:
`i(w') = e.symm(w')` (as `E`-elements).

`≤`: `i(w') = ⋃_{X ∈ w'} i(↑X) = ⋃_{X ∈ w'} e.symm(↑X)`, and each `e.symm(↑X) ≤ e.symm(w')` by
`principal_le_of_mem` and monotonicity of `e.symm`.

`≥`: the family `c(X) := e.symm(↑X)` (`X ∈ w'`) is directed with sup exactly `i(w')` (`hS_eq`
below, "for free" from the membership formula), hence `a`-fixed (`toElementMap_iSupDirected_fixed`).
Algebraicity of `w'` in `F` reduces `w' ≤ e(i(w'))` to checking `↑X ≤ e(i(w'))` for each `X ∈ w'`,
which (applying `e.symm`) is exactly `c(X) ≤ i(w')` — true since `i(w')` is the sup of the `c`
family. -/
theorem toElementMap_sectionMap (w' : F.Element) :
    (sectionMap e).toElementMap w' = (e.symm w').1 := by
  have hdirC : ∀ i j : {X : Set β // w'.mem X}, ∃ k : {X : Set β // w'.mem X},
      (e.symm (F.principal (w'.sub i.2))).1 ≤ (e.symm (F.principal (w'.sub k.2))).1 ∧
        (e.symm (F.principal (w'.sub j.2))).1 ≤ (e.symm (F.principal (w'.sub k.2))).1 :=
    fun i j => ⟨⟨i.1 ∩ j.1, w'.inter_mem i.2 j.2⟩,
      e.symm.monotone ((F.principal_le_iff (w'.sub i.2) (w'.sub (w'.inter_mem i.2 j.2))).mpr
        Set.inter_subset_left),
      e.symm.monotone ((F.principal_le_iff (w'.sub j.2) (w'.sub (w'.inter_mem i.2 j.2))).mpr
        Set.inter_subset_right)⟩
  have hS_eq : (sectionMap e).toElementMap w' =
      iSupDirected (fun i : {X : Set β // w'.mem X} => (e.symm (F.principal (w'.sub i.2))).1)
        hdirC := by
    apply Element.ext
    intro Z
    rw [toElementMap_mem_iff_principal, mem_iSupDirected]
    constructor
    · rintro ⟨X, hX, hZ⟩; rw [toElementMap_sectionMap_principal] at hZ; exact ⟨⟨X, hX⟩, hZ⟩
    · rintro ⟨⟨X, hX⟩, hZ⟩; exact ⟨X, hX, by rwa [toElementMap_sectionMap_principal]⟩
  have hfixC : ∀ i : {X : Set β // w'.mem X},
      a.toElementMap (e.symm (F.principal (w'.sub i.2))).1 =
        (e.symm (F.principal (w'.sub i.2))).1 :=
    fun i => (e.symm (F.principal (w'.sub i.2))).2
  apply le_antisymm
  · rw [hS_eq]
    apply iSupDirected_le
    intro i
    exact e.symm.monotone (principal_le_of_mem i.2)
  · have hSfix : a.toElementMap ((sectionMap e).toElementMap w') =
        (sectionMap e).toElementMap w' := by
      rw [hS_eq]; exact toElementMap_iSupDirected_fixed _ hdirC hfixC
    have key : w' ≤ e ⟨(sectionMap e).toElementMap w', hSfix⟩ := by
      refine le_trans (le_of_eq (eq_iSupDirected_principal w'))
        (iSupDirected_le _ (principalFamily_directed w') ?_)
      intro i
      have : e.symm (F.principal (w'.sub i.2)) ≤ ⟨(sectionMap e).toElementMap w', hSfix⟩ := by
        show (e.symm (F.principal (w'.sub i.2))).1 ≤ (sectionMap e).toElementMap w'
        rw [hS_eq]
        exact le_iSupDirected _ hdirC i
      have := e.monotone this
      rwa [e.apply_symm_apply] at this
    have := e.symm.monotone key
    rwa [e.symm_apply_apply] at this
end HardDirection

section HardDirection

variable {a : ApproximableMap E E}

variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)

/-- **`e` distributes over directed sups of `a`-fixed families.** `Fix(a)` is not itself a
`NeighborhoodSystem.Element` type, so this is proved directly by antisymmetry (rather than via a
generic "order isos preserve directed sups" lemma): both inequalities reduce to `le_iSupDirected`/
`iSupDirected_le` on the `E`- and `F`-sides plus monotonicity of `e`/`e.symm`. -/
theorem e_apply_iSupDirected_fixed {I : Type u} [Nonempty I] (d : I → E.Element)
    (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k) (hfix : ∀ i, a.toElementMap (d i) = d i)
    (hSfix : a.toElementMap (iSupDirected d hdir) = iSupDirected d hdir)
    (hdir' : ∀ i j : I, ∃ k, e ⟨d i, hfix i⟩ ≤ e ⟨d k, hfix k⟩ ∧
      e ⟨d j, hfix j⟩ ≤ e ⟨d k, hfix k⟩) :
    e ⟨iSupDirected d hdir, hSfix⟩ = iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' := by
  apply le_antisymm
  · have hstep : (⟨iSupDirected d hdir, hSfix⟩ : FixSet a) ≤
        e.symm (iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir') := by
      show iSupDirected d hdir ≤ _
      apply iSupDirected_le
      intro i
      show d i ≤ _
      have hle : e ⟨d i, hfix i⟩ ≤ iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' :=
        le_iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' i
      have := e.symm.monotone hle
      rwa [e.symm_apply_apply] at this
    have := e.monotone hstep
    rwa [e.apply_symm_apply] at this
  · apply iSupDirected_le
    intro i
    exact e.monotone (le_iSupDirected d hdir i)

end HardDirection

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}

/-- **Compact elements are principal** — the converse of `principal_isCompactElt`, via
algebraicity: test compactness against `x`'s own principal-approximant family. -/
theorem eq_principal_of_isCompactElt {x : V.Element} (hx : IsCompactElt x) :
    ∃ (X : Set γ) (hX : V.mem X), x = V.principal hX := by
  have hle : x ≤ iSupDirected (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2))
      (principalFamily_directed x) := le_of_eq (eq_iSupDirected_principal x)
  obtain ⟨i0, hi0⟩ :=
    hx (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2)) (principalFamily_directed x) hle
  exact ⟨i0.1, x.sub i0.2, le_antisymm hi0 (principal_le_of_mem i0.2)⟩

end Algebraic

/-- **`fixedNbhd a ◁ E`, unconditionally.** The consistency clause is the same monotonicity +
intersectivity calculation as `fixedNbhd`'s own `inter_mem`, just without needing the extra
consistency witness `Z`. -/
theorem fixedNbhd_subsystem (a : ApproximableMap E E) : fixedNbhd a ◁ E where
  master_eq := rfl
  sub := fun h => h.1
  inter_closed := by
    rintro X Y ⟨hXE, hXa⟩ ⟨hYE, hYa⟩ hEXY
    have h1 : a.rel (X ∩ Y) X := a.mono hXa Set.inter_subset_left subset_rfl hEXY hXE
    have h2 : a.rel (X ∩ Y) Y := a.mono hYa Set.inter_subset_right subset_rfl hEXY hYE
    exact ⟨hEXY, a.inter_right h1 h2⟩

/-- **The "easy" (`⟸`) half of formula (ii), isolated.** Valid for **any** approximable map
`a : E → E` with **no hypothesis on `a` at all** — not even that `a` satisfies the rest of formula
(ii), let alone that it is a finitary projection. Pure monotonicity + up-closure: `↑X ≤ x`
(`principal_le_of_mem`) pushes `a`'s self-relation at `X` up to `x` (`toElementMap_mono`), and
`X ⊆ Y` finishes by up-closure. Isolated from `isFinitaryProjection_of_formula`'s own proof (where
it was the `←` branch of the `constructor`) because Exercise 8.27(b)(3) needs exactly this half,
unconditionally, for `a := piD d` — independently of whether the *rest* of formula (ii) holds. -/
theorem mem_of_exists_rel_self {a : ApproximableMap E E} (x : E.Element) {Y : Set α}
    (hYE : E.mem Y) {X : Set α} (hXx : x.mem X) (hXY : X ⊆ Y) (hXaX : a.rel X X) :
    (a.toElementMap x).mem Y := by
  have hX : E.mem X := a.rel_dom hXaX
  have hmem : (a.toElementMap (E.principal hX)).mem X := (a.rel_iff_mem_principal hX).mp hXaX
  have hle : E.principal hX ≤ x := principal_le_of_mem hXx
  have hXmem : (a.toElementMap x).mem X := (a.toElementMap_mono hle) X hmem
  exact (a.toElementMap x).up_mem hXmem hYE hXY

/-- **Theorem 8.5, `(ii) ⟹ (i)` (Scott 1981, PRG-19).** If `a` satisfies Scott's step-closure
formula `a(x) = {Y ∈ E ∣ ∃X∈x, X⊆Y ∧ XaX}` for every `x ∈ |E|`, then `a` is a finitary projection.

The proof shows `a` literally *is* `retractionOfSubsystem` for `D = fixedNbhd a`: unwinding formula
(ii) at a principal `x = ↑X` via `rel_iff_mem_principal` reproduces exactly
`retractionOfSubsystem_rel`'s formula. Definition 8.3's corollaries of Proposition 8.2 then finish
the proof — no further work needed. -/
theorem isFinitaryProjection_of_formula (a : ApproximableMap E E)
    (hii : ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X) :
    FinitaryProjection a := by
  have heq : a = Subsystem.retractionOfSubsystem (fixedNbhd_subsystem a) := by
    apply ApproximableMap.ext
    intro X Z
    rw [Subsystem.retractionOfSubsystem_rel]
    constructor
    · intro hr
      have hX : E.mem X := a.rel_dom hr
      have hmem : (a.toElementMap (E.principal hX)).mem Z := (a.rel_iff_mem_principal hX).mp hr
      obtain ⟨hZE, Y, hXY, hYZ, hYa⟩ := hii (E.principal hX) |>.mp hmem
      exact ⟨hX, hZE, Y, ⟨a.rel_dom hYa, hYa⟩, (E.mem_principal hX).mp hXY |>.2, hYZ⟩
    · rintro ⟨hX, hZ, Y, ⟨_, hYa⟩, hXY, hYZ⟩
      exact (a.rel_iff_mem_principal hX).mpr
        (mem_of_exists_rel_self (E.principal hX) hZ (E.mem_principal hX |>.mpr ⟨a.rel_dom hYa, hXY⟩)
          hYZ hYa)
  rw [heq]
  exact Subsystem.isFinitaryProjection_retractionOfSubsystem (fixedNbhd_subsystem a)

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}

/-- **Principal elements are compact**: if `↑X ⊑ ⋃ᵢ dᵢ` for a directed family, then already
`↑X ⊑ dᵢ` for some single `i`. Immediate from `X ∈ ↑X` and `mem_iSupDirected`. -/
theorem principal_compact {X : Set γ} (hX : V.mem X) {I : Type*} [Nonempty I]
    (d : I → V.Element) (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k)
    (h : V.principal hX ≤ iSupDirected d hdir) : ∃ i, V.principal hX ≤ d i := by
  obtain ⟨i, hi⟩ := (mem_iSupDirected d hdir).mp (h X ⟨hX, subset_rfl⟩)
  exact ⟨i, fun _ ⟨hW, hXW⟩ => (d i).up_mem hi hW hXW⟩

theorem principal_isCompactElt {X : Set γ} (hX : V.mem X) : IsCompactElt (V.principal hX) :=
  fun d hdir h => principal_compact hX d hdir h

end Algebraic

section HardDirection

variable {a : ApproximableMap E E}

/-- Idempotency of a retraction at the element level: `a(a(z)) = a(z)`. -/
theorem toElementMap_idem {a : ApproximableMap E E} (ha : Retraction a) (z : E.Element) :
    a.toElementMap (a.toElementMap z) = a.toElementMap z := by
  rw [← toElementMap_comp a a z, ha.out]

end HardDirection

section HardDirection

variable {a : ApproximableMap E E}

variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)

/-- **Scott's compactness-reflection fact.** If `e.symm(w')` is a *principal* (finite) element of
`F`, then `e.symm(w')`'s image `.1` in `E` need not be principal; the content here is the converse
direction: **pulling a genuinely principal element of `F` back through `e.symm` always lands on a
principal element of `E`.** The key step lifts compactness across the retraction: any `E`-directed
family bounding `(e.symm(↑Y)).1` from above can be replaced (applying the continuous, idempotent
`a`) by an `a`-fixed directed family with the same sup-relationship, and `a ≤ idMap E` (`a` is a
*projection*, not just a retraction) is exactly what lets the bound transfer back down. -/
theorem exists_principal_eq_of_isRetraction_le_idMap (ha_ret : Retraction a)
    (ha_proj : a ≤ idMap E) {Y : Set β} (hY : F.mem Y) :
    ∃ (X : Set α) (hX : E.mem X), (e.symm (F.principal hY)).1 = E.principal hX := by
  apply eq_principal_of_isCompactElt
  intro I _ d hdir hle
  set d2 : I → E.Element := fun i => a.toElementMap (d i) with hd2
  have hdir2 : ∀ i j, ∃ k, d2 i ≤ d2 k ∧ d2 j ≤ d2 k := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, a.toElementMap_mono hik, a.toElementMap_mono hjk⟩
  have hfix2 : ∀ i, a.toElementMap (d2 i) = d2 i := fun i => toElementMap_idem ha_ret (d i)
  have hle2 : (e.symm (F.principal hY)).1 ≤ iSupDirected d2 hdir2 := by
    calc (e.symm (F.principal hY)).1 = a.toElementMap (e.symm (F.principal hY)).1 :=
          (e.symm (F.principal hY)).2.symm
      _ ≤ a.toElementMap (iSupDirected d hdir) := a.toElementMap_mono hle
      _ = iSupDirected d2 hdir2 := toElementMap_iSupDirected a d hdir
  have hSfix2 : a.toElementMap (iSupDirected d2 hdir2) = iSupDirected d2 hdir2 :=
    toElementMap_iSupDirected_fixed d2 hdir2 hfix2
  have hdir2' : ∀ i j : I, ∃ k, e ⟨d2 i, hfix2 i⟩ ≤ e ⟨d2 k, hfix2 k⟩ ∧
      e ⟨d2 j, hfix2 j⟩ ≤ e ⟨d2 k, hfix2 k⟩ := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hdir2 i j
    exact ⟨k, e.monotone hik, e.monotone hjk⟩
  have hle3 : F.principal hY ≤ iSupDirected (fun i => e ⟨d2 i, hfix2 i⟩) hdir2' := by
    have h1 : e ⟨(e.symm (F.principal hY)).1, (e.symm (F.principal hY)).2⟩ ≤
        e ⟨iSupDirected d2 hdir2, hSfix2⟩ := e.monotone hle2
    rwa [Subtype.coe_eta, e.apply_symm_apply,
      e_apply_iSupDirected_fixed e d2 hdir2 hfix2 hSfix2 hdir2'] at h1
  obtain ⟨i0, hi0⟩ := principal_isCompactElt hY _ _ hle3
  have hi0' : e.symm (F.principal hY) ≤ ⟨d2 i0, hfix2 i0⟩ := by
    have := e.symm.monotone hi0
    rwa [e.symm_apply_apply] at this
  have hfinal : (e.symm (F.principal hY)).1 ≤ d2 i0 := hi0'
  have hd2le : d2 i0 ≤ d i0 := by
    have := (le_iff_toElementMap_le.mp ha_proj) (d i0)
    rwa [toElementMap_idMap] at this
  exact ⟨i0, hfinal.trans hd2le⟩

/-- **Theorem 8.5, `(i) ⟹ (ii)` (Scott 1981, PRG-19), assembled.** If `a` is a finitary projection,
it satisfies Scott's step-closure formula.

Given `Y ∈ a(x)`: since `a` is idempotent, `w := a(x)` is itself `a`-fixed, and `e ⟨w, _⟩ : F.Element`
decomposes (Exercise 2.9, via `sectionMap`'s `Claim′`) as a union of `sectionMap e`'s values on
`F`-principals `↑W` for `W ∈ e ⟨w, _⟩`; picking the `W` witnessing `Y`, compactness reflection turns
`(e.symm ↑W).1` into a genuine `E`-principal `↑X`. `X ⊆ Y` and `X a X` both come from `X`'s defining
equation `a(↑X) = ↑X` (inherited from `FixSet`); `x.mem X` comes from `↑X ≤ w = a(x) ≤ x` (the last
step using `a ≤ I_E`). -/
theorem formula_of_isFinitaryProjection {a : ApproximableMap E E} (h : FinitaryProjection a) :
    ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X := by
  obtain ⟨⟨ha_ret, ha_proj⟩, β, F, ⟨e⟩⟩ := h.out
  intro x Y
  constructor
  · intro hY
    have hw : a.toElementMap (a.toElementMap x) = a.toElementMap x := toElementMap_idem ha_ret x
    set w : E.Element := a.toElementMap x with hw_def
    have hYw : w.mem Y := hY
    have hclaim : (sectionMap e).toElementMap (e ⟨w, hw⟩) = w := by
      rw [toElementMap_sectionMap e (e ⟨w, hw⟩), e.symm_apply_apply]
    have hYsec : ((sectionMap e).toElementMap (e ⟨w, hw⟩)).mem Y := by rw [hclaim]; exact hYw
    obtain ⟨W, hW, hYW⟩ := (toElementMap_mem_iff_principal (sectionMap e) (e ⟨w, hw⟩)).mp hYsec
    rw [toElementMap_sectionMap_principal] at hYW
    obtain ⟨X, hX, hXeq⟩ :=
      exists_principal_eq_of_isRetraction_le_idMap e ha_ret ha_proj ((e ⟨w, hw⟩).sub hW)
    rw [hXeq] at hYW
    obtain ⟨hYE, hXY⟩ := (E.mem_principal hX).mp hYW
    have hfixX : a.toElementMap (E.principal hX) = E.principal hX := by
      rw [← hXeq]; exact (e.symm (F.principal ((e ⟨w, hw⟩).sub hW))).2
    have haXX : a.rel X X := (a.rel_iff_mem_principal hX).mpr (by
      rw [hfixX]; exact (E.mem_principal hX).mpr ⟨hX, subset_rfl⟩)
    have hprincipal_le_w : E.principal hX ≤ w := by
      have h1 : F.principal ((e ⟨w, hw⟩).sub hW) ≤ e ⟨w, hw⟩ :=
        principal_le_of_mem hW
      have h2 : e.symm (F.principal ((e ⟨w, hw⟩).sub hW)) ≤ e.symm (e ⟨w, hw⟩) :=
        e.symm.monotone h1
      have h3 : (e.symm (F.principal ((e ⟨w, hw⟩).sub hW))).1 ≤ w := by
        have := h2
        rwa [e.symm_apply_apply] at this
      rwa [hXeq] at h3
    have hw_le_x : w ≤ x := by
      have := (le_iff_toElementMap_le.mp ha_proj) x
      rwa [toElementMap_idMap] at this
    have hXx : x.mem X := hprincipal_le_w.trans hw_le_x X ((E.mem_principal hX).mpr ⟨hX, subset_rfl⟩)
    exact ⟨hYE, X, hXx, hXY, haXX⟩
  · rintro ⟨hYE, X, hXx, hXY, hXaX⟩
    exact mem_of_exists_rel_self x hYE hXx hXY hXaX

end HardDirection

end
end DomainTheory.NeighbourhoodSystems

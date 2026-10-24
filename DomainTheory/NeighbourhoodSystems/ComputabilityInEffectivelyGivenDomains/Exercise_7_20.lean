module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_11
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_10

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_19

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*}
/- concordance: source L4675 EXERCISE 7.20 union on power domains -/
/-- **Exercise 7.20 (Scott 1981, PRG-19) — the flattening combinator `union : ℙ(ℙD) → ℙD`.** Given a
`ℙℙD`-neighbourhood `A` and a `ℙD`-neighbourhood `B`, the relation holds iff every `D`-neighbourhood
`X` occurring in some member-set `S ∈ A` is covered by some `Y ∈ B`. This is the
representation-independent form of Scott's displayed `∀ i<n ∀ j<m_i ∃ k<q. X_{ij} ⊆ Y_k`
(see `unionMap_rel_fin`). It is the multiplication `μ` of the power-domain monad. -/
def unionMap (V : NeighborhoodSystem α) :
    ApproximableMap V.PowerDomain.PowerDomain V.PowerDomain where
  rel A B := V.PowerDomain.PDmem A ∧ V.PDmem B ∧ ∀ S ∈ A, ∀ X ∈ S, ∃ Y ∈ B, X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨V.PowerDomain.PDmem_master, V.PDmem_master, ?_⟩
    intro S hS X hX
    simp only [mem_upSet] at hS
    exact ⟨V.master, ⟨V.master_mem, subset_rfl⟩, V.sub_master (V.PDmem_mem hS.1 hX)⟩
  inter_right := by
    rintro A B B' ⟨hA, hB, hbody⟩ ⟨-, hB', hbody'⟩
    refine ⟨hA, V.PDmem_inter hB hB', ?_⟩
    intro S hS X hX
    obtain ⟨Y, hYB, hXY⟩ := hbody S hS X hX
    obtain ⟨Y', hY'B', hXY'⟩ := hbody' S hS X hX
    have hXmem : V.mem X := V.PDmem_mem (V.PowerDomain.PDmem_mem hA hS) hX
    have hYmem : V.mem Y := V.PDmem_mem hB hYB
    have hY'mem : V.mem Y' := V.PDmem_mem hB' hY'B'
    have hsub : X ⊆ Y ∩ Y' := Set.subset_inter hXY hXY'
    have hinmem : V.mem (Y ∩ Y') := V.inter_mem hYmem hY'mem hXmem hsub
    exact ⟨Y ∩ Y', Set.mem_inter
      (V.PDmem_down hB hYB Set.inter_subset_left hinmem)
      (V.PDmem_down hB' hY'B' Set.inter_subset_right hinmem), hsub⟩
  mono := by
    rintro A A' B B' ⟨_, _, hbody⟩ hA'A hBB' hA' hB'
    refine ⟨hA', hB', ?_⟩
    intro S hS X hX
    obtain ⟨Y, hYB, hXY⟩ := hbody S (hA'A hS) X hX
    exact ⟨Y, hBB' hYB, hXY⟩
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*}

@[simp] theorem unionMap_rel {V : NeighborhoodSystem α} {A : Set (Set (Set α))} {B : Set (Set α)} :
    (unionMap V).rel A B ↔ V.PowerDomain.PDmem A ∧ V.PDmem B ∧ ∀ S ∈ A, ∀ X ∈ S, ∃ Y ∈ B, X ⊆ Y :=
  Iff.rfl
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*}

/-- **Exercise 7.20 — the relation of `union` at the level of `ℙℙ𝒟`/`ℙ𝒟`-codes.** For any
presentation `Q` of `ℙ𝒟` whose `c`-th neighbourhood is `Y_c = ⋃_{a∈dl c} ↓Xₐ` (e.g. the
`PDPresentation` of Proposition 7.10), and the canonical enumeration `(ℙℙ𝒟).Ypd Q` of `ℙℙ𝒟`,
`(union).rel ((ℙℙ𝒟).Ypd Q n) (ℙ𝒟.Ypd P m) ↔ ∀ c ∈ dl n, ∀ a ∈ dl c, ∃ b ∈ dl m, Xₐ ⊆ X_b`. -/
theorem unionMap_rel_Ypd_iff {V : NeighborhoodSystem α} (P : ComputablePresentation V)
    (Q : ComputablePresentation V.PowerDomain) (hQ : ∀ c, Q.X c = V.Ypd P c) {n m : ℕ} :
    (unionMap V).rel (V.PowerDomain.Ypd Q n) (V.Ypd P m)
      ↔ ∀ c ∈ decodeList n, ∀ a ∈ decodeList c, ∃ b ∈ decodeList m, P.X a ⊆ P.X b := by
  constructor
  · rintro ⟨-, -, hbody⟩ c hc a ha
    have hSmem : Q.X c ∈ V.PowerDomain.Ypd Q n :=
      (V.PowerDomain.mem_Ypd Q).mpr ⟨c, hc, Q.mem_X c, subset_rfl⟩
    have hXinS : P.X a ∈ Q.X c := by
      rw [hQ c]; exact (V.mem_Ypd P).mpr ⟨a, ha, P.mem_X a, subset_rfl⟩
    obtain ⟨Y, hYB, hXY⟩ := hbody (Q.X c) hSmem (P.X a) hXinS
    obtain ⟨b, hb, hYin⟩ := (V.mem_Ypd P).mp hYB
    exact ⟨b, hb, hXY.trans hYin.2⟩
  · intro hgen
    refine ⟨V.PowerDomain.Ypd_isPDmem Q n, V.Ypd_isPDmem P m, ?_⟩
    intro S hS X hX
    obtain ⟨c, hc, hScod⟩ := (V.PowerDomain.mem_Ypd Q).mp hS
    have hXinQ : X ∈ Q.X c := hScod.2 hX
    rw [hQ c] at hXinQ
    obtain ⟨a, ha, hXin⟩ := (V.mem_Ypd P).mp hXinQ
    obtain ⟨b, hb, hab⟩ := hgen c hc a ha
    exact ⟨P.X b, (V.mem_Ypd P).mpr ⟨b, hb, P.mem_X b, subset_rfl⟩, hXin.2.trans hab⟩
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*}

/-- The empty power-domain neighbourhood lies under every intersection of neighbourhoods. -/
theorem ypd_zero_subset_inter {V : NeighborhoodSystem α} (P : ComputablePresentation V) (a b : ℕ) :
    V.Ypd P 0 ⊆ V.Ypd P a ∩ V.Ypd P b := by
  rw [V.Ypd_zero P]
  exact Set.empty_subset _

/-- **Exercise 7.20 (Scott's first question) — `union` is computable.** Given `P : Computable
Presentation 𝒟` with a primitive-recursive consistency decider `consV`, `union` is a computable map
between the canonical presentations of `ℙℙ𝒟` and `ℙ𝒟` (Proposition 7.10). The inner consistency
decider of `ℙ𝒟` (needed to build the `ℙℙ𝒟` presentation) is the constant decider `fun _ => 1`,
correct because the empty union (`code 0`, `Y₀ = ∅`) lies below every `ℙ𝒟`-neighbourhood. The
relation is in fact recursively *decidable* (a nested bounded `∀∀∃` over `P.incl_computable`). -/
theorem unionMap_isComputable {V : NeighborhoodSystem α} (P : ComputablePresentation V)
    (consV : ℕ → ℕ) (hconsVp : Nat.Primrec consV)
    (hconsVs : ∀ a b, consV (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    ComputableMap
      (V.PowerDomain.PDPresentation (V.PDPresentation P consV hconsVp hconsVs)
        (fun _ => 1) (Nat.Primrec.const 1)
        (fun a b => ⟨fun _ => ⟨0, ypd_zero_subset_inter P a b⟩, fun _ => rfl⟩))
      (V.PDPresentation P consV hconsVp hconsVs)
      (unionMap V) := by
  constructor
  have hrd : RecDecidable₂ (fun n m => ∀ c ∈ decodeList n, ∀ a ∈ decodeList c,
      ∃ b ∈ decodeList m, P.X a ⊆ P.X b) := (V.subCode_computable P).bForallList
  have key : RecDecidable₂ (fun n m => (unionMap V).rel
      (V.PowerDomain.Ypd (V.PDPresentation P consV hconsVp hconsVs) n) (V.Ypd P m)) := by
    refine RecDecidable.of_iff (fun t => ?_) hrd
    exact unionMap_rel_Ypd_iff P (V.PDPresentation P consV hconsVp hconsVs) (fun _ => rfl)
  exact key.re
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*}

/-- **Exercise 7.20 — Scott's displayed formula.** On generators (nested finite lists of down-sets)
`(union).rel (⋃_{l∈LS} ↓_{ℙD}(⋃_{X∈l} ↓X)) (⋃_{Y∈LY} ↓Y) ↔ ∀ l ∈ LS, ∀ X ∈ l, ∃ Y ∈ LY, X ⊆ Y`,
exactly Scott's `∀ i<n ∀ j<m_i ∃ k<q. X_{ij} ⊆ Y_k`. (`→` reads off the generators `X_{ij}`; `←`
extends to all members by downward closure at both levels and `⊆`-monotonicity of the target.) -/
theorem unionMap_rel_fin (V : NeighborhoodSystem α) {LS : List (List (Set α))} {LY : List (Set α)}
    (hLS : ∀ l ∈ LS, ∀ X ∈ l, V.mem X) (hLY : ∀ Y ∈ LY, V.mem Y) :
    (unionMap V).rel (⋃ l ∈ LS, V.PowerDomain.upSet (⋃ X ∈ l, V.upSet X)) (⋃ Y ∈ LY, V.upSet Y)
      ↔ ∀ l ∈ LS, ∀ X ∈ l, ∃ Y ∈ LY, X ⊆ Y := by
  constructor
  · rintro ⟨-, -, hbody⟩ l hl X hX
    have hXmem : V.mem X := hLS l hl X hX
    have hSinA : (⋃ X ∈ l, V.upSet X) ∈ ⋃ l ∈ LS, V.PowerDomain.upSet (⋃ X ∈ l, V.upSet X) :=
      Set.mem_iUnion₂.mpr ⟨l, hl, (⟨l, hLS l hl, rfl⟩ : V.PDmem _), subset_rfl⟩
    have hXinS : X ∈ ⋃ X' ∈ l, V.upSet X' := (V.mem_PDunion).mpr ⟨X, hX, hXmem, subset_rfl⟩
    obtain ⟨Y, hYB, hXY⟩ := hbody _ hSinA X hXinS
    obtain ⟨Y', hY', hYin⟩ := (V.mem_PDunion).mp hYB
    exact ⟨Y', hY', hXY.trans hYin.2⟩
  · intro hgen
    refine ⟨?_, ⟨LY, hLY, rfl⟩, ?_⟩
    · refine ⟨LS.map (fun l => ⋃ X ∈ l, V.upSet X), ?_, ?_⟩
      · intro S hS
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hS
        exact ⟨l, hLS l hl, rfl⟩
      · ext z
        simp only [Set.mem_iUnion, List.mem_map, exists_prop]
        constructor
        · rintro ⟨l, hl, hz⟩
          exact ⟨_, ⟨l, hl, rfl⟩, hz⟩
        · rintro ⟨S, ⟨l, hl, rfl⟩, hz⟩
          exact ⟨l, hl, hz⟩
    · intro S hS X hX
      obtain ⟨l, hl, hSin⟩ := Set.mem_iUnion₂.mp hS
      have hXin : X ∈ ⋃ X' ∈ l, V.upSet X' := hSin.2 hX
      obtain ⟨X', hX', hXmem⟩ := (V.mem_PDunion).mp hXin
      obtain ⟨Y, hY, hX'Y⟩ := hgen l hl X' hX'
      exact ⟨Y, (V.mem_PDunion).mpr ⟨Y, hY, hLY Y hY, subset_rfl⟩, hXmem.2.trans hX'Y⟩
end

section
set_option linter.unusedVariables false

theorem example_720.{u_1} : And
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V) (consV : Nat → Nat)
      (hconsVp : Nat.Primrec consV)
      (hconsVs :
        ∀ (a b : Nat),
          Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                (@Inter.inter (Set α) (@Set.instInter α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b)))),
      @DomainTheory.NeighbourhoodSystems.ComputableMap (Set (Set α)) (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
          (fun (x : Nat) => @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Nat.Primrec.const (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) fun (a b : Nat) =>
          @Iff.intro
            (@Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set (Set α)) (@Set.instLE (Set α))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs) k)
                (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    b)))
            (fun
                (x :
                  @Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
              @Exists.intro Nat
                (fun (k : Nat) =>
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@DomainTheory.NeighbourhoodSystems.ypd_zero_subset_inter α V P a b))
            fun
              (x :
                ∃ (k : Nat),
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b))) =>
            @rfl Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
        (@DomainTheory.NeighbourhoodSystems.unionMap α V))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)),
      (∀ (c : Nat),
          @Eq (Set (Set α))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q c)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)) →
        ∀ {n m : Nat},
          Iff
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set (Set α)) (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.unionMap α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q n)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P m))
            (∀ (c : Nat),
              @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList n) c →
                ∀ (a : Nat),
                  @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
                    ∃ (b : Nat),
                      And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList m) b)
                        (@LE.le (Set α) (@Set.instLE α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b)))))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {LS : List (List (Set α))}
    {LY : List (Set α)},
    (∀ (l : List (Set α)),
        @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l →
          ∀ (X : Set α),
            @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X) →
      (∀ (Y : Set α),
          @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y) →
        Iff
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set (Set α)) (Set α)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
            (@DomainTheory.NeighbourhoodSystems.unionMap α V)
            (⋃ (l : List (Set α)),
              ⋃ (_ : @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet (Set α)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (⋃ (X : Set α),
                    ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))
            (⋃ (Y : Set α),
              ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V Y))
          (∀ (l : List (Set α)),
            @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l →
              ∀ (X : Set α),
                @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X →
                  ∃ (Y : Set α),
                    And (@Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y)
                      (@LE.le (Set α) (@Set.instLE α) X Y))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V) (consV : Nat → Nat)
      (hconsVp : Nat.Primrec consV)
      (hconsVs :
        ∀ (a b : Nat),
          Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                (@Inter.inter (Set α) (@Set.instInter α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b)))),
      @DomainTheory.NeighbourhoodSystems.ComputableMap (Set (Set α)) (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
          (fun (x : Nat) => @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Nat.Primrec.const (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) fun (a b : Nat) =>
          @Iff.intro
            (@Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set (Set α)) (@Set.instLE (Set α))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs) k)
                (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    b)))
            (fun
                (x :
                  @Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
              @Exists.intro Nat
                (fun (k : Nat) =>
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@DomainTheory.NeighbourhoodSystems.ypd_zero_subset_inter α V P a b))
            fun
              (x :
                ∃ (k : Nat),
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b))) =>
            @rfl Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
        (@DomainTheory.NeighbourhoodSystems.unionMap α V))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)),
      (∀ (c : Nat),
          @Eq (Set (Set α))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q c)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)) →
        ∀ {n m : Nat},
          Iff
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set (Set α)) (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.unionMap α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q n)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P m))
            (∀ (c : Nat),
              @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList n) c →
                ∀ (a : Nat),
                  @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
                    ∃ (b : Nat),
                      And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList m) b)
                        (@LE.le (Set α) (@Set.instLE α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b)))))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {LS : List (List (Set α))}
    {LY : List (Set α)},
    (∀ (l : List (Set α)),
        @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l →
          ∀ (X : Set α),
            @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X) →
      (∀ (Y : Set α),
          @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y) →
        Iff
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set (Set α)) (Set α)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
            (@DomainTheory.NeighbourhoodSystems.unionMap α V)
            (⋃ (l : List (Set α)),
              ⋃ (_ : @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet (Set α)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (⋃ (X : Set α),
                    ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X),
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))
            (⋃ (Y : Set α),
              ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V Y))
          (∀ (l : List (Set α)),
            @Membership.mem (List (Set α)) (List (List (Set α))) (@List.instMembership (List (Set α))) LS l →
              ∀ (X : Set α),
                @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) l X →
                  ∃ (Y : Set α),
                    And (@Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) LY Y)
                      (@LE.le (Set α) (@Set.instLE α) X Y)))
  (@And.intro
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V) (consV : Nat → Nat)
      (hconsVp : Nat.Primrec consV)
      (hconsVs :
        ∀ (a b : Nat),
          Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                (@Inter.inter (Set α) (@Set.instInter α)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b)))),
      @DomainTheory.NeighbourhoodSystems.ComputableMap (Set (Set α)) (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
          (fun (x : Nat) => @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Nat.Primrec.const (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) fun (a b : Nat) =>
          @Iff.intro
            (@Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (∃ (k : Nat),
              @LE.le (Set (Set α)) (@Set.instLE (Set α))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs) k)
                (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                    b)))
            (fun
                (x :
                  @Eq Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
              @Exists.intro Nat
                (fun (k : Nat) =>
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@DomainTheory.NeighbourhoodSystems.ypd_zero_subset_inter α V P a b))
            fun
              (x :
                ∃ (k : Nat),
                  @LE.le (Set (Set α)) (@Set.instLE (Set α))
                    (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
                      k)
                    (@Inter.inter (Set (Set α)) (@Set.instInter (Set α))
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp
                          hconsVs)
                        b))) =>
            @rfl Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
        (@DomainTheory.NeighbourhoodSystems.unionMap α V))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation (Set α)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)),
      (∀ (c : Nat),
          @Eq (Set (Set α))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q c)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)) →
        ∀ {n m : Nat},
          Iff
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set (Set α)) (Set α)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.unionMap α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) Q n)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P m))
            (∀ (c : Nat),
              @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList n) c →
                ∀ (a : Nat),
                  @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
                    ∃ (b : Nat),
                      And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList m) b)
                        (@LE.le (Set α) (@Set.instLE α)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
    @DomainTheory.NeighbourhoodSystems.unionMap_isComputable @DomainTheory.NeighbourhoodSystems.unionMap_rel_Ypd_iff)
  @DomainTheory.NeighbourhoodSystems.unionMap_rel_fin
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β : Type*}

end
end DomainTheory.NeighbourhoodSystems
end

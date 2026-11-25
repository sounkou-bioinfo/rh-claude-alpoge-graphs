# Lattice construction in the Lean RH proof: what the gain–slope link is made of

Source: `/tmp/rh-src/orig/src` at commit 40e56bab. Paths below are relative to it.
Working notes with more line references: `/tmp/rh-agent/notes.md`.

Abbreviations for long paths:

- `CGE28` = `Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean`
- `TPE` = `Formalism/LocalToGlobal/Divisibility/TwistedPlaceEtaSumLeExtended.lean`
- `RecBridge` = `Formalism/LocalToGlobal/Divisibility/RecBridge.lean`
- `QLD` = `Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean`
- `TopD` = `Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean`
- `PlacesP` = `Formalism/LocalToGlobal/GlobalTheory/PlacesP.lean`
- `IRZ` = `Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean`
- `LRC` = `Formalism/LocalRingCardinality`
- `SUT` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/SetUnipotentTranslate.lean`
- `ELP` = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLedPart.lean`
- `EFK` = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsFamPOfKits.lean`

## Short answer

1. There are two lattice families. `D.div.Nu u` (one per word `u`) and `D.div.RR`. Both are
   data fields of `D7.div : DivData`. `slope_bounds`/`BoundsMu` controls the dual slope of `RR`.
   The gain `Ga` enters through `Nu u`, not through `RR`.
2. The statement that ties `Ga` to a lattice slope is `SlopesN_at` (`QLD:181`). It is proved
   from hypotheses, in three layers. I read the three layers. The innermost fact is
   **definitional**: `Nu u` is defined as the lattice `NuLat u` twisted by the ideal
   `∏ p_w^(-⌊e_w · sg(u,w)⌋)`, and `sg` is defined as `Σ_j (gain + F − E)`. `NprimeDef` is
   discharged by `rfl`.
3. So the equation "slope(Nu) = slope(NuLat) + gain terms" has no arithmetic content of its
   own. It is the degree formula for an ideal twist, applied to a lattice that was twisted by
   the gain on purpose.
4. The arithmetic content is in other statements. They say that this twisted lattice still
   pairs integrally into `RR` (`val2`, `OneMapIntoCC`) with bounded height (`HBound`, `hTie`),
   and that the local index of `NuLat` in `MramL` is bounded by `tau + io`. I read where
   these enter. I did not read their proofs to the bottom. See "What is still open".
5. I found one degenerate object in the RH cone: a toy `D7` with zero-dimensional lattices.
   The declarations I read use it only for a `Nonempty D7` statement. I did not establish
   whether it also seeds the family `Fm.D x i`.

## Summary table

| Declaration | File:line | Read | Kind |
|---|---|---|---|
| `HLat` (V, basis `b`, Gram `X`, lattice `L`) | `LRC/DataArith.lean:61` | read | definition (structure) |
| `DivData` (`RR`, `Nu`, `Bk`, `h`, …) | `LRC/DataArith.lean:139` | read | definition; lattices are free data fields |
| `D7.div` | `LRC/RhoDetPrimeEqMuTildeMulChiPow.lean:114` | read (field only) | data field |
| `SizeData₂` (`gain`, `F`, `E`, `tau`, `io`, `NuLat`, `lenMN`) | `LRC/DataParams₂.lean:76` | read | data fields |
| `SizeData₂.sg`, `Ga`, `Fo`, `NuH` | `LRC/DataParams₂.lean:215-236` | read | definitions |
| `DV.MramL`, `DV.Iu`, `DV.NprimeDef`, `DV.NuDef`, `DV.RRDef`, `lenLoc` | `LRC/DataDIVDefs.lean:12-54` | read | definitions (Props) |
| `FamP` fields `nuDef`, `nprimeDef`, `rrDef`, `h_eq` | `Formalism/SharpRestriction/ParConsts.lean:71-74` | read | hypothesis fields |
| `famOfKits` | `EFK:56` | read | repackages kit fields into `FamP` |
| `setDiv`, `nPrime`, `LedPart.pt` | `SUT:25, 372, 381` | read | definitional; `nprimeDef := fun _ => rfl`, `h_eq := fun _ => rfl` |
| `setLat` | `ELP:187` | read | definitional; `lenMN` := measured length |
| `exists_lat`, `exists_ledPart` | `ELP:119, 195` | read | proved from hypotheses `RecOK`, `LedOK` |
| `NP` (local lattice at gain places) | `IRZ:464` | read | definition, non-trivial |
| `VV`, `tauP`, `ioP`, `gainP` | `IRZ:292-358` | read | definitions |
| `LT.Nlam` (local lattice at T places) | `LRC/DataLatDefs.lean:96` | not read | – |
| `mu_index_sum`, `mu_eq`, `muMax_le` | `PlacesP:61, 129, 171` | read | proved from hypotheses |
| `places_at_of` | `PlacesP:297` | read | proved from hypotheses |
| `HypLow`, `HypLow2`, `HypHigh` | `Formalism/SizeWindowBrackets/ClaimGaFree.lean:65-97` | read | definitions (real-number Props) |
| `Places_at`, `slopesN_at_of`, `slopesNF_of` | `TopD:1516, 1529, 1544` | read | proved from `Places_at` |
| `SlopesN_at` | `QLD:181` | read | definition (the Ga–slope Prop) |
| `M.data` | `QLD:464` | read | definition (record) |
| `placesF_of` | `PlacesP:638` | not read (statement only) | – |
| `BoundsMu` | `Formalism/DivisorInequality/StatementObj.lean` | read | definition (Prop) |
| `Formalism.DivisorInequality.boundsMu` / `slope_bounds` proof | – | not read | – |
| `IndefData.RR`, `muCC`, `abelian₂` | `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean` | read | definitions |
| `DivInputs0R`, `DivInputsR`, `DivClausesR` | `CGE28:26, 105, 111` | read | hypothesis structures / Prop |
| `divClausesR_of` | `CGE28:184` | read | proved from `DivInputsR` |
| `DivInputsDef3.toDivInputs0R` | `TPE:247` | read | fills `LG`, `E2`, `E3`, `gy`, `bi`, `biv` with proved lemmas |
| `DivisionPackageFace` (`hNu`, `hRR`, `shift`, `hTie`, `foTie`, `rhs`, `inp`) | `RecBridge:601` | read | hypothesis structure |
| `DivisionPackageFace.wordFacts` | `RecBridge:633` | read | proved; `val2` derived here |
| `val2AllAtRF`, `nu_into` | – | not read | – |
| `DivisionPackageFace.ofOpen`, `DivisionPackageColumns.ofTied` | – | not read | the only builders of the package (graph) |
| `LinkDIV_at` | `Formalism/SharpRestriction/GlobalTheoremInputs.lean:77` | read | definition (Prop) |
| `fmZeroHLat`, `toyZeroLatticeDatum`, `exampleRecordOfData` | `LRC/SpanPowerMembership/FmZeroHLatEmpty.lean:159`, `…/ExampleClassGroupCardPos.lean:82-132` | read in part | degenerate (zero lattice), in RH cone |
| `exists_divStage` (builds a real `DivData`) | `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEmbeddingMemUnitGroup.lean:282` | statement only | proved (not read) |

## 1. The lattices and how they are built

### 1.1 The objects

A Hermitian lattice is plain data (`LRC/DataArith.lean:61-72`, read): a vector space `V`
over the number field, a basis `b`, one Gram matrix `X v` for each infinite place, and an
`𝓞 K`-submodule `L`. The slope is `mu := HN.muDef b X L` (`:84`).

`DivData` (`LRC/DataArith.lean:139-160`, read) has fields `RR : HLat`, `Nu : Words → HLat`,
`Bk` (a pairing for each word), `h` (a height for each word). These are free fields. The
record of step 5 reads them directly (`QLD:464-505`, read):

- `d := (D.div.Nu u).rank`, `muN := (D.div.Nu u).mu`, `h := D.div.h u`
- `muM := ((D.fm u).lat 0).mu`, `muCC := D.div.RR.muDual`
- `Fo := L.Fo`, `Ga := L.Ga`, with `D = Fm.D x (M.pt u0)`, `L = Fm.L x (M.pt u0)`

### 1.2 `Nu u` for the family: a twist by the gain, by definition

`SizeData₂` carries `gain`, `F`, `E`, `tau`, `io` as plain real-valued functions and
`NuLat`, `lenMN` as free fields (`LRC/DataParams₂.lean:91-200`, read). From them
(`LRC/DataParams₂.lean:212-220`, read, paraphrased):

- `gainD` is `gain` set to 0 on the `drop` places.
- `sg u w := Σ_{j ∈ lifts} (gainD j w + F j w − E u j w)`
- `Ga := Σ_{w ∈ supp} sz w ((Σ_j gainD j w) − tau w)`, with `sz w y := 2 · lwP w · (ramIdx w · y)`

The twist ideal and the tie (`LRC/DataDIVDefs.lean:17-24`, read, paraphrased):

- `Iu D L u := ∏_{w ∈ L.supp} (D.plEq w).asIdeal ^ (−⌊ur D w (L.sg u w)⌋)`, `ur D w y := ramIdx w * y`
- `NprimeDef D L := ∀ u, (D.div.Nu u).L = span {a • y | a ∈ Iu D L u, y ∈ L.NuLat u}`

`NprimeDef` is a Prop. For the family it is true by construction (`SUT`, read):

- `setDiv D N h` (`SUT:25-31`) overwrites `Nu u` by `{D.div.Nu u with L := N u}` and `h` by the
  given `h`. It keeps `V`, the basis, the Gram matrices and `RR`.
- `nPrime L u := span {a • y | a ∈ DV.Iu D L u, y ∈ L.NuLat u}` (`SUT:372-373`).
- `LedPart.pt` (`SUT:381-401`) sets `D := setDiv D (nPrime p.L) p.ht`, with
  `ht := DV.hExpl6 D p.L Y.X C.Csz` (`SUT:379`), and discharges
  `nprimeDef := fun _ => rfl` (`SUT:398`) and `h_eq := fun _ => rfl` (`SUT:400`).

`famOfKits` (`EFK:56-147`, read) takes `D x i`, `L x i`, `nuDef`, `nprimeDef`, `rrDef`, `h_eq`
from these kit points. The graph shows three more builders of `FamP.mk` in the cone
(`UpperTheory.GalC.gd`, `EX.DC.setTu`, `FamP.raise`). Not read.

### 1.3 `NuLat u`: glued from local lattices

`exists_lat` (`ELP:119-185`, read, proved from hypotheses `hfull`, `hT`, `hS`) gives a
submodule `N` of `(D.div.Nu u).V` such that:

- at a gain place (`VV ≠ ∅`): `x` is locally in `N` iff `c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg`
- at a place over `T`: locally in `N` iff `D.nuIn u x ∈ LT.Nlam D u w`
- elsewhere: `N` is locally inside `MramL`, and equal to it where `VV = ∅`

`MramL D u := ((D.fm u).lat 0).L.comap (D.nuIn u)` (`LRC/DataDIVDefs.lean:12`, read).

The local lattice `NP` is a real construction (`IRZ:464-472`, read):

```lean
  Submodule.span G.O {F' | ∃ VV' ⊆ VVp, ∃ F ∈ G.M,
      F' = yProd Y u w hg VV' (((p : G.O) ^ (∑ t0 ∈ VVp \ VV', ⌈Sv X K (aL L) (bL L) p t0⌉.toNat)) • F)} ⊓
    G.M.map (((p : G.O) ^ ⌈tauP X K (aL L) (bL L) p⌉.toNat) • LinearMap.id) ⊓ Y.Vram u w hg
```

`setLat` then sets `NuLat := N` and defines `lenMN` as the measured length (`ELP:187-190`, read):

```lean
    lenMN := fun u w => ((DV.lenLoc (D.plEq w) (N u) (DV.MramL D u)).toNat : ℚ) / (D.what₂.places.ramIdx w : ℚ) }
```

So the third clause of `NuDef` (`lenLoc = lenMN * ramIdx`) holds by this definition
(`hlen`, `ELP:207-214`). The first two clauses come from `exists_lat`.

`exists_ledPart` (`ELP:195-227`, read) is proved from `RecOK s C cD D` and
`LedOK s C cD ch Y a b`. I did not read who proves these two.

### 1.4 `RR`, the lattice whose dual slope `slope_bounds` controls

On the indefinite-forms side, `RR := glueLat fun w => matLat (ι (μ w)) (abelian₂ (μ w))` and
`muCC := muDef dual XE (dualLat RR)` (`IndefSide.lean`, read). `BoundsMu` concludes an upper
bound for that `muDef` (`StatementObj.lean`, read).

The link to `D.div.RR` is a hypothesis field: `hRR : HLatTie D.div.RR Pk.core.cols.RR
Pk.core.cols.XE eRR` (`RecBridge:601-629`, read). The same holds for `Nu`
(`hNu`, `shift : NuC (wU u) = shiftLat (Nu u) (sgRec L u)`). The family also carries
`rrDef : DV.RRDef D`, passed from `Lay.rrDef` (`SUT:83-119`), a field.

## 2. The statement that relates `Ga` to a slope

The statement (`QLD:181-183`, read, paraphrased):

- `SlopesN_at L C := ∀ u,`
  `(Nu u).muMax ≤ (lat 0).muMax + L.Ga + L.Fo − L.Ee u + C·m·B0`
  `∧ (lat 0).mu + L.Ga + L.Fo − L.Ee u − LoU L C u ≤ (Nu u).mu`

Its proof has three layers.

**Layer A, algebra (proved).** `slopesN_at_of` (`TopD:1529-1539`, read) derives `SlopesN_at`
from `Places_at` by real-number algebra (`lower_bound_simplified`, `claimHigh_valid`,
`Ga_eq`, `Fo_eq`, `linarith`). `Places_at` (`TopD:1516-1525`) asserts `HypLow`, `HypLow2`,
`HypHigh`. The key clause of `HypLow` (`ClaimGaFree.lean:65-72`, read) is an equation:

- `muN = muMu + Sg W l sg' tau − BeSum W l du len tau`, with `Sg := Σ_w 2·l w·(sg' w − tau w)`

**Layer B, lattice identities (proved from hypotheses).** `places_at_of` (`PlacesP:297-437`,
read) supplies the witnesses `sg' w := ⌊ur (L.sg u w)⌋ / ramIdx w`, `muMu := (MuH D u).mu`.
It gets the equation from `mu_eq` (`PlacesP:129-169`, read):

- `(D.div.Nu u).mu = (MuH D u).mu + Σ_w 2·lwP w·⌊ur (L.sg u w)⌋ − (Σ_w 2·lwP w·(lenMN u w · ramIdx w)) / rank`

`mu_eq` uses two real lattice facts. `J.mu_diff` is the slope change under an ideal twist
(statement not read; used at `PlacesP:129-169`). `mu_index_sum` (`PlacesP:61-104`, read,
proved) is the slope change for a finite-index sublattice. `mu_eq` takes `NprimeDef`,
`NuDef`, `NuCommens` as hypotheses.

**Layer C, the tie to gain (definitional).** `NprimeDef` is `rfl` for the family (§1.2).
`sg` is a `def` built from `gainD`. `Ga` is a `def` built from `gainD` and `tau`.

Verdict for the equation: the gain appears in `slope(Nu u)` because `Nu u` is defined as the
gain-twist of `NuLat u`. The proof of that step is `rfl` plus the degree formula. This is
"definitional", in the sense of the task. It is not vacuous: the degree formula and the
index formula are real lemmas, and they are needed to get a slope out of the definition.

The inequality parts of `Places_at` are not definitional:

- `hG1` in `places_at_of`: `NuLat` is locally inside `p^⌊ur tau⌋ · MramL`, and
  `lenMN ≤ duS·(tau + io)`. This is a hypothesis of `places_at_of`. It bounds the local index
  of `NP` and is where `tau`, `io` earn their place in `Ga`.
- `h26 : adm26`, `hMu : NprimeMuR`, `hTa`: hypotheses of `places_at_of`. Providers not read.

### `Fo` and `h`

- `Fo`: `foTie : 2 * FoOfR Pk.core = L.Fo` is a field of `DivisionPackageFace`
  (`RecBridge:601-629`). `FoOfR` is `Σ_j Σ_{y∈Tw} lw y * (ramw y * N.F0 y j)` (`CGE28:20`).
  The term enters `BoundsMu` as `2 ΣΣ lw·Fy`. Hypothesis at this level. Provider not read.
- `h`: `D.div.h u = hExpl6 …` holds by `rfl` (`SUT:400`). The content is the claim that the
  pairing has height at most `h`: the clause `htMap … (D.div.Bk u) ≤ D.div.h u` in
  `LinkDIV_at` (`GlobalTheoremInputs.lean:77-89`), and the field
  `hTie : (R u).hu − meanLog κ = D.div.h u`. Hypothesis fields at the level I read.
- `LG` in `boundBR` is not a gain sum. `toDivInputs0R` (`TPE:247-286`, read) sets
  `LG := lgDef R s` (equal to `lam0 + log s` by `rfl`, `TPE:288`), `E3 := 1`, and fills `bi`
  with `gram_valuation_le_extended` (`TPE:20-28`, proved). It bounds valuations of a Gram
  determinant.

## 3. Where the gain lattice meets `slope_bounds`

`divClausesR_of` (`CGE28:184-247`, read) proves `DivClausesR` (`CGE28:111-121`) from
`I : DivInputsR`. The four clauses, paraphrased:

1. The pairing maps `shiftLat Nu sg` into `dualLat RR`.
2. An operator-norm bound.
3. `muCC − meanLog κ + hu − 2·FoOfR ≤ R.rhs`. This uses
   `Formalism.DivisorInequality.boundsMu` and `I.L3main`.
4. `muDef (shiftLat Nu sg) = muDef Nu + 2 Σᶠ lw · shiftZ sg`. Again the twist formula.

Clause 1 is the divisibility statement. It needs `val2` (`CGE28:105`): the valuation of the
pairing on `Nu × Mt` is at least `sg w`. In the cone, `val2` is not a free field. It is
derived at `RecBridge:639-641` (read):

```lean
        val2 := Formalism.L2.G.ServJointF.val2AllAtRF D L _ P.brTied hcut h2 u (P.Nu u)
          (Formalism.L2.G.ServJoint.nu_into L hN u (P.eNu u) (P.NuC (P.wU u)) (P.Nu u) (P.hNu u).lat (P.shift u)) })
```

Its inputs are `brTied`, `CutUp`, `adm2`, `NprimeDef`. I did not read `val2AllAtRF`.

So the logical shape is the standard one: a lattice `Nu`, twisted up by the gain, still maps
into the dual of `RR` with height at most `h`. Then `slope(Nu) ≤ slope bound for RR^∨ + h`
forces the gain to be small. In this shape the gain–slope equation is free. The price is
paid in clause 1 (`val2`) and in the height bound.

## 4. Vacuity checks

What I checked, and the result:

- **`True` bodies / `if … else True`:** none in the declarations listed as "read" above. I did
  not query `vt` for the whole sub-cone.
- **Nielsen-vacuous dependence:** the graph marks `vac = false` for `FamP.mk` users,
  `DivisionPackageFace.ofOpen`, `exists_ledPart`, `placesF_min'`, `slopesNF_of`, `LedPart.mk`
  users, `RecOK.mk` user.
- **Definitions that make a relation an identity:** yes, three.
  `nprimeDef := fun _ => rfl` (`SUT:398`), `h_eq := fun _ => rfl` (`SUT:400`), and `lenMN`
  defined as the measured length (`ELP:187-190`). Also
  `Rd := Σ 2·lE w·(L.sg u w − ⌊ur sg⌋/e)` closed by `le_refl _` in `places_at_of`.
  These are honest "define the object, then compute" steps, not hidden assumptions. They do
  mean that `SlopesN`'s equation part proves nothing about primes.
- **`gainP` can be zero:** `VV := if Cand D L K p ∧ Sig … ≤ x^(-eps) then goodReps X p else ∅`
  (`IRZ:292-293`). `tauP` is 0 when `VV = ∅` (`IRZ:341-344`). `gainP` is 0 when
  `(IsResidueClassZero D p ∧ hP D p = 0) ∨ X'' < p` (`IRZ:355-358`). When `VV = ∅` the glued
  lattice equals `MramL` locally and `lenMN = 0`. I did not establish whether `VV` is
  non-empty for a useful set of primes. If `VV` were always empty, the whole gain side would
  be trivial. This needs a check on the loss side (`ASK − Ga`).
- **Degenerate lattices:** `fmZeroHLat` is `V := Fin 0 → K`, `X := fun _ => 0`, `L := ⊤`
  (`FmZeroHLatEmpty.lean:159-164`, read). `exampleRecordOfData` sets
  `div := toyZeroLatticeDatum H.E` (`ExampleClassGroupCardPos.lean:110`, read). Both are in the
  RH cone. The graph chain is `exampleRecord → nonempty_D7_of_localGap →
  record_nonempty_of_localGap → GlobalTheory.MemLoc.record_nonempty →
  GlobalTheory.WachPlace.exists_positions_global`. `nonempty_D7_of_localGap` only states
  `Nonempty D7` (`LRC/SpanPowerMembership.lean:49`, read). I did not read
  `exists_positions_global`.
  This matters because `setDiv` keeps `V`. If a kit's seed `D7` were the toy, then `Nu u`
  would live in a zero-dimensional space, `rank = 0`, and every slope statement would be
  degenerate. A separate real constructor exists: `exists_divStage`
  (`LatticeEmbeddingMemUnitGroup.lean:282`, statement read) gives `Nu u` with
  `(Nu u).L.map nuIn = (C.fm u).ramL`. `Lat_at` (`QLD:185`) also demands `rank > 0`. Which
  `D7` reaches `Kit` is **not established**.
- **Unused slots:** not checked.

## 5. Plain statement

- The link "total local gain `Ga` ↔ slope of the lattice `Nu`" is proved in Lean, and I read
  the proof chain from `SlopesN_at` down to `rfl`. Its equation part is definitional: the
  lattice is built by twisting with the gain. It carries no information about primes.
- The link has real content in four places. I read the statements, not the proofs:
  1. the local lattice `NP` and its index bound against `tau + io` (`hG1`,
     `LatticeLengthsAtPlace`);
  2. the divisibility `val2` (pairing valuation ≥ `sg`), derived by `val2AllAtRF`;
  3. the height bound for the pairing (`HBound` clause of `LinkDIV_at`, `hTie`);
  4. `boundsMu` / `slope_bounds` for `RR`, with the ties `hRR`, `hNu`, `shift`, `foTie`.
- Items 3 and 4 enter through the structure `DivisionPackageFace`, whose fields are
  hypotheses at the level I read. The graph shows one builder, `DivisionPackageFace.ofOpen`,
  called by `DivisionPackageColumns.ofTied`. Until those are read, "the gain is bounded by
  the lattice slope through a proved statement" is **not established** end to end.

## What is still open

1. `DivisionPackageFace.ofOpen` and `DivisionPackageColumns.ofTied`: how `inp`, `hNu`, `hRR`,
   `shift`, `hTie`, `foTie`, `rhs` are discharged. This is the main gap.
2. `Formalism.L2.G.ServJointF.val2AllAtRF` and `ServJoint.nu_into`: the proof of local
   divisibility. Also the provider of `brTied` and `CutUp`.
3. The proof of `Formalism.DivisorInequality.boundsMu` (`slope_bounds`). I read only the
   statement `BoundsMu`.
4. `placesF_of` (`PlacesP:638`) and its caller at
   `GlobalSchurBounds/LossesSmallShares.lean:505`: who supplies `hG1`, `adm26`, `NprimeMuR`.
   Also `placesF_min'` (`GlobalTheory/PlacesMin.lean:23`).
5. Providers of `RecOK` (graph: `GlobalTheory.Mem.Top.LayOfCore.lay_of_core`) and `LedOK`
   (no `.mk` users found; it may be a `def`). Not read.
6. Which `D7` seeds the kits: the toy `exampleRecord` or a `DivStage` from
   `exists_divStage`. Read `GlobalTheory.WachPlace.exists_positions_global` and the `Kit`
   structure.
7. Whether `VV` is non-empty for the primes that matter, so that `gainP`, `tauP`, `NP` are
   not trivially zero / equal to `MramL`.
8. `IndefData.ON` and `L3` (fields of the indefinite side) and `LT.Nlam`: not read.
9. The other `FamP.mk` builders (`GalC.gd`, `EX.DC.setTu`, `FamP.raise`): not read.
10. A `vt` (body `True`) scan restricted to the forward cone of `SlopesNF` and `LinkDIV`.

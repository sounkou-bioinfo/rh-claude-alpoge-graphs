# notes (working)
- CGE28 = Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean (320 lines)
  - FoOfR :20 = Σ_j Σ_{y∈Tw} lw y * (ramw y * N.F0 y j)   (def)
  - boundBR :23 = Σ l3 + 2 FoOfR + LG + Σ(E1+E2) + E3
  - DivInputs0R :26-103 structure of hypotheses: Nu_lat, sg_fin, Xc_unit, a_pos, X0, ch: ColChain, hn, nP, cb, nKcb, eig6, eb, heb(IsLocBasis Df0.abelian₂), Sy, Sy_tw, G0, LG,E3,E2,gy,ηy, bi (vw y (Gm..) ≤ D*gy y), bLG (Σ lw*gy ≤ LG), biv, borderedMinorImage, twisted_third_sum_le, El3, L3main, errB, Q, de0, deQ, Q1, Qb, la_le, constant_ge_twenty_eight
  - DivInputsR :105 extends with val2 (valuation of pairing Pt ≥ sg w on Nu × Mt)
  - DivClausesR :111-121: (B u maps shiftLat Nu sg into dualLat RR) ∧ opnorm bound ∧ muCC - meanLog κ + hu - 2 FoOfR ≤ R.rhs ∧ muDef shiftLat = muDef Nu + 2 Σᶠ lw*shiftZ sg
  - divClausesR_of :184 ; linkDIV_L2R_clauses :265 (A : FamIn ...) ; linkDIV_L2R :286
- StatementObj.lean (Formalism/DivisorInequality): BoundsMu : Prop def. conclusion: muDef dual(XE)(dualLat R) ≤ meanLog κ + Σ lcv(XW j)(M j)/D + 2 ΣΣ lw*Fy + LG + Σ(E1+E2) + E3  ∧ ∀ j, lcv/D = -muDef (XW j)(M j). R hypothesis: localization of R at y = localization of matLat (ι (μ y)) (abelian₂ (μ y)); abelian₂ μ0 = matLat Pm Mt.
- IndefSide.lean (Formalism/LocalToGlobal/IndefiniteForms): DefBase, DefSide (HV, Mt, Pq, XQ, HT, XT, Tl...), DefSide.abelian₂ t := matLat (Pq t) (Mt t); Gm := gramR (quotGram Pq HV) eb; WF; DefCols (Mem,a,Xc,Pt); IndefNum (F0,J0,E1,l3,l6,hh,la,de); IndefData (μ,Tw,D,XE,Ep,ι,dW,XW,Wp,M,θ,κ,lam,err0); RR := glueLat fun w => matLat (ι (μ w)) (abelian₂ (μ w)); muCC := muDef dual XE (dualLat RR); L3: lcv(XW j)(M j)/D ≤ N.l3 j ; ON ; FUN; IndefCore{base,cols,extra}
- divClausesR_of (CGE28:184-247): hyp I : DivInputsR. clause1 via P.cols.intoDual divIntoDualShift latticeGlue ... I.val2; clause 3: hB := P.base.boundsMu Formalism.DivisorInequality.boundsMu specDet reduction_lemma_zero latticeGlue ramBasic wf0 P.extra.untw I.eb I.heb I.Sy ... I.bi I.bLG I.biv ...; gives P.base.muCC ≤ meanLog κ + Σ l3 + 2ΣΣ lw*(ramw*F0) + LG + Σ(E1+E2)+E3 ; then passage (P.extra.passage) base→cols; then I.L3main; R.divIneq. clause4 via shiftMu.
- linkDIV_L2R (CGE28:286-318): hyp Pk : IndefPkgR A.fam.amb (faceOf A ...) cf C CH, I : DivInputsR Pk.core R x Nu sg; wf from A.side_WF hOk ...
- TPE = Formalism/LocalToGlobal/Divisibility/TwistedPlaceEtaSumLeExtended.lean
  - gram_valuation_le_extended :20-28 (proved, via A3.A.fam.GmOf_le): vw y (Gm (ebOf) (μ y) y) ≤ D * vw y (|G|*s)
  - lift_index_bound_extended :30-63 (proved from h11 : LiftExponentAtTwisted hypothesis, lift_lattices, exponent_weight_spectral, fam.jw_le)
  - twisted_place_eta_sum_le_extended :65-98 (from hN : InEta hyp)
  - DivInputsDef3 :104-170 structure: remaining hypotheses: Nu_lat, sg_fin, Xc_unit, a_pos, X0, ch, hn, nP, cb, nKcb, eig6, bd, hN: InEta, h11: LiftExponentAtTwisted, dg, dg_dvd, hG0, El3, L3main, errB, Q.., constant_ge_twenty_eight
  - DivInputsDef3.toDivInputs0R :247-286: eb := ebOf, heb := ebOf_spec, Sy := SyOf, G0 := gram_det_unit_outside, LG := lgDef R s (= lam0 + log s, by defs_eq :288 rfl), E3 := 1, E2 := etaSumBound, gy := fun y => vw y (|G|*s), bi := gram_valuation_le_extended, bLG := bLG_def, biv := lift_index_bound_extended, twisted_third_sum_le := places_ell_weighted_sum_le_one
  => LG is NOT a prime gain sum: it is log|G| + log s bound on Gram-det valuation. The F0 term (Fo = FoOfR) enters through IndefData.ON (index bound at Tw places) which is a FIELD of IndefSide (to check where proved).
- QLD = Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean (1892 lines)
  - M.data :464-505: d := (D.div.Nu u).rank, muN := (D.div.Nu u).mu, muMaxN := .muMax, h := D.div.h u, muM := ((D.fm u).lat 0).mu, muCC := D.div.RR.muDual, muMinCC := D.div.RR.muMinDual, Fo := L.Fo, Ga := L.Ga, Ta := Σ_{w∈L.supp} sz w (L.tau w)   [D = Fm.D x (M.pt u0), L = Fm.L x (M.pt u0)]
  - **SlopesN_at :181-183** = ∀ u, (D.div.Nu u).muMax ≤ ((D.fm u).lat 0).muMax + L.Ga + L.Fo - L.Ee u + C*m*B0 ∧ ((D.fm u).lat 0).mu + L.Ga + L.Fo - L.Ee u - LoU L C u ≤ (D.div.Nu u).mu   <-- THE Ga↔slope link
  - SlopesM_at :173 bounds lat 0 mu/muMax ; Lat_at :185 (rank>0, mu ≤ muMax, RR.muMinDual = -RR.muMax); Frame_at :188 ; Loss_at :203 (ASK - L.Ga ≤ ...)
  - SlopesNF :254 := ∃ C x0, 0 ≤ C ∧ ∀ x ≥ x0, ∀ i, SlopesN_at (Fm.L x i) C
  - data_DIV :580 hypothesis h: RR.muDual + div.h u - L.Fo ≤ MAIN u + ...
  - linkGLOBAL :1879
- LevelOfCongruence.lean (Formalism/SizeWindowBrackets/ChainSlopeWindows): Ga_bound5 :113, each_unit_bound_statement :175
- GSB = Formalism/SharpRestriction/GlobalSchurBounds
  - TopDensityNGeSixteen.lean: Places_at :1516-1525 (∃ sg' de muMu muMaxMu PT Rd LT RX, UnitWeightPartition.HypLow L.supp (suppT L u) lifts lE L.gainD L.F (L.E u) L.tau L.io lenMN sg' duS (Nu u).rank de muMu (Nu u).mu PT Rd ∧ HypLow2 ... ((D.fm u).lat 0).mu muMu ... ∧ HypHigh ... lat0.muMax muMaxMu (Nu u).muMax ∧ LT ≤ .. ∧ RX ≤ ..)
  - slopesN_at_of :1529-1539 (proved: lower_bound_simplified + claimHigh_valid + Ga_eq, Fo_eq, Ee_eq' + linarith); PlacesF :1541; slopesNF_of :1544
  - callers: LinkMin.lean:714 (placesF_min'), LossesSmallShares.lean:505 (placesF_of Fm crystallineComparison h10 tSet hTu hRank lG lMu), FrameCodeOfAdditive.lean:44 slopes_family_of_division_side (from SlopeLemmaFamily)
- ClaimGaFree.lean (Formalism/SizeWindowBrackets), ns Formalism.LFunctionChainParameters.UnitWeightPartition; pure real-number algebra over Finset:
  - sgw J gain F E w := Σ_{j∈J} (gain j w + F j w - E j w)  :11
  - Ga W J l gain tau := 2 Σ_{w∈W} l w * ((Σ_j gain j w) - tau w) :14 ; Fo :17 ; Ee :20 ; Sg W l s tau := Σ 2 l w (s w - tau w) :23; Ta; IO; be du len tau w := (len w - du*tau w)/du; BeSum :35
  - HypLow :65-72: ... ∧ Σ_{W} 2 l w (sgw w - sg' w) ≤ Rd ∧ **muN = muMu + Sg W l sg' tau - BeSum W l du len tau**
  - HypLow2 :80-84: muMu = muM - f log(T-1)/(T-2) ∧ ...
  - HypHigh :94-97: sg' w ≤ sgw w ∧ muMaxN ≤ muMaxMu + Sg W l sg' tau ∧ muMaxMu ≤ muMaxM
  - ClaimLow/ClaimHigh are algebraic consequences.
  => Ga-to-slope link reduces to: muN (slope of Nu u) EQUALS muMu + Σ 2 l_w (sg'_w - tau_w) - BeSum. Must find who proves this (places_at_of, PlacesP.lean:297; placesF_of :638; placesF_min' PlacesMin.lean:23)
- PlacesP.lean (Formalism/LocalToGlobal/GlobalTheory, 796 lines)
  - mu_index_sum :61-104 (proved; real: muDef b X N = muDef b X M - (Σ_{v∈S} 2 lw v * lenLoc v N M)/rk M for N ≤ M same rank; uses slopeLatticeData.muDef_index, index_finsupp)
  - rk_nu :124 ; mu_eq :129-169 (proved from hyps hN' : DV.NprimeDef D L, hNu : DV.NuDef D L, hc : NuCommens D L, hle : L.NuLat u ≤ DV.MramL D u, hoff): (D.div.Nu u).mu = (MuH D u).mu + Σ_{w∈supp} 2 lwP w * ⌊DV.ur D w (L.sg u w)⌋ - (Σ 2 lwP w * (L.lenMN u w * ramIdx w))/rank. Uses J.mu_diff, hNu.2.2 (lenLoc = lenMN*ramIdx), `(L.NuH u).mu = muDef .. (L.NuLat u) := rfl`, hN' u : (D.div.Nu u).L = idealSmul (DV.Iu D L u) (L.NuLat u)
  - muMax_le :171-243 (proved from DV.LocLe hyps): (Nu u).muMax ≤ (MuH D u).muMax + Σ 2 lwP (⌊ur (sg u w)⌋ - k w)
  - lenLoc_atT_zero :260 ; places_at_of :297 ; placesF_of :638 : PlaceConditionsFamily
  - places_at_of :297-437 (proved from hyps hN' NprimeDef, hNu NuDef, hc NuCommens, hrank, h26 : adm26 L C26, hMu : NprimeMuR L CMu, hG1 (LocLe at ⌊ur tau w⌋₊ of NuLat in MramL ∧ lenMN ≤ duS*(tau+io)), htauN, hio, htauT, hoff, hTa, hT2,hT4,hT1). Witnesses: sg' w := ⌊DV.ur D w (L.sg u w)⌋ / ramIdx w ; muMu := (MuH D u).mu ; Rd := Σ 2 lE w (L.sg u w - ⌊ur(sg)⌋/e) with `le_refl _` for HypLow's Σ 2 l (sgw J gainD F E w - sg' w) ≤ Rd => sgw J gainD F (E u) w is DEFEQ to L.sg u w (check SizeData₂.sg). The muN equation comes from mu_eq. HypHigh from muMax_le with k w = ⌊ur(tau w)⌋₊.
  - So chain: Nu.L = Iu • NuLat (NprimeDef) ; slope(Nu) = slope(NuLat) + Σ 2 lw ⌊e·sg⌋ (J.mu_diff) ; slope(NuLat) = slope(MramL) - Σ 2 lw len/rank (mu_index_sum). sg = Σ_j(gainD+F-E).
- DataDIVDefs.lean (Formalism/LocalRingCardinality), ns Formalism.BasicNotions.DV:
  - MramL D u := ((D.fm u).lat 0).L.comap (D.nuIn u) :12 ; ur D w y := ramIdx w * y :15
  - Iu D L u := ∏_{w∈L.supp} (D.plEq w).asIdeal ^ (-(⌊ur D w (L.sg u w)⌋)) :17-20
  - NprimeDef D L : Prop := ∀ u, (D.div.Nu u).L = span {a•y | a ∈ Iu, y ∈ L.NuLat u} :22-24   (a PROP on D.div.Nu, not a def of Nu)
  - RRDef D : Prop :26-29 (x ∈ D.div.RR.L ↔ ∀ w ∃ d ∉ p_w, d•x ∈ span{y | D.jEE y ∈ D.what₂.RRset (muAt w)})
  - LocLe :31, LocEq :35, lenLoc :39 (Module.length of localized B/(A∩B))
  - NuDef D L : Prop :48-54 (NuLat ⊆loc MramL away from T; LocEq at drop/non-inert places; lenLoc = lenMN*ramIdx)
- DataArith.lean: HLat structure :61-72 (V, ι, b basis, X : InfinitePlace → Matrix, L submodule); mu := HN.muDef b X L :84 ; muMax; muDual; DivData structure :139-160 fields RR : HLat, Nu : Words → HLat, Bk, h, HH, HH_ge, etaF, Dall, delP. OneMapIntoCC :176, HBound :178 are Props.
- DataParams₂.lean (Formalism/LocalRingCardinality): structure SizeData₂ (D : D7) :76-200. FREE FIELDS: supp :91, gain/F/E/tau/io :93-97 (plain real-valued functions), *_supp, gain_g :104, untwisted :108, not_inert :110 (gain=0,tau=0,io=0 at non-inert), drop :113, F_conj, F_above, NuLat : ∀ u, Submodule (𝓞 LL) (D.div.Nu u).V :135 (free field!), lenMN : Word → Pl → ℚ :200 (free field).
  defs: lwP :203, sz w y := 2*lwP w*(ramIdx w*y) :205, lifts := Icc 1 m :208, gainD :212 (0 on drop else gain), sg u w := Σ_{j∈lifts}(gainD j w + F j w - E u j w) :215, Fo :218, Ga := Σ_{w∈supp} sz w ((Σ_j gainD j w) - tau w) :220, Ee :222, NuH u := {D.div.Nu u with L := L.NuLat u} :236
- RhoDetPrimeEqMuTildeMulChiPow.lean: structure D7 :76; fields div : DivData LL Word :114 (FREE FIELD: RR, Nu, Bk, h are data), div_good :116 (Gram dets units), plEq :134, jEE :185, fm : ∀ u, MemberForms ... :285, nuIn :291 (+inj, range = (fm u).ramSub). NuFull :359, RRFull :356 Props.
=> Lattices Nu u, RR, NuLat are structure DATA; ties are Props NprimeDef/NuDef/RRDef/NuCommens/NuAtT. Next: who proves these for Fm.D x i / Fm.L x i (FamP, ParConsts.lean:31).
- ParConsts.lean (Formalism/SharpRestriction): structure FamP eps extends FamCore eps :31-80+. FamCore (FamCore.lean:71): D : ∀ x, Ix x → D7 :82 ; L : ∀ x i, SizeData₂ (D x i) :83 — DATA fields. FamP FIELDS (hypotheses): lats0 :64, latTied :68, nuDef :71 (DV.NuDef), nprimeDef :72 (DV.NprimeDef), rrDef :73 (DV.RRDef), h_eq :74 (div.h u = DV.hExpl6 ...), ex : Extra ... :78.
  => question becomes: who constructs a FamP (FamP.mk / FamCore.mk) in the RH cone, with what D, L, and how nuDef/nprimeDef are discharged.
- Graph: FamP.mk used (in c_rh, not vac) by: GlobalTheory.EX.famOfKits (def), UpperTheory.GalC.gd (def), GlobalTheory.EX.DC.setTu (def), FamP.raise. FamCore.mk: famOfKits, gd, raise.
  SizeData₂.mk: UpperTheory.GalC.Tr.ledBack, Wts.sizeData₂, GlobalTheory.EX.OB.ledTr, EX.exists_sizeData_explicit, EX.Led.setLat, GlobalTheory.Refill.refill, GalC.Gen.ledTr
  DivData.mk: GlobalTheory.EX.OB.setDiv, **Formalism.BasicNotions.Examples₂.toyZeroLatticeDatum (in c_rh!)**, Mem.DivModel.exists_divStage, Mem.DivInhab.exists_divStage, Mem.R3.Refill.to, Mem.R3.LedRec.exists_bare, Mem.R3.Rw.exists_divStage_of_pk
  HLat.mk: ... Examples₂.fmZeroHLat (c_rh), EX.OB.setDiv, Mem.DivInhab.subHLat, Mem.R3.Refill.ofDiv, ProvRowSide.stdHLat, PeriodClassSum.formsLat ...
- ExistsFamPOfKits.lean (Development/AbelianVarietyTheory/Proofs/GlobalInterpolation): famOfKits :56-147: D x i := ((k x).pt i.1).D ; L x i := ((k x).pt i.1).L ; nuDef := ((k x).pt i.1).xa.nuDef ; nprimeDef := ...xa.nprimeDef ; rrDef := ...xa.rrDef ; h_eq := ...xa.h_eq ; lats0/latTied := ...ta.*. exists_famP_of_kits :149 (hyp: k : ∀ s ..., Kit C cD ch s). So FamP is repackaged from `Kit` points; need Kit / point structure (fields xa, ta) and who builds them.
- SUT = Development/AbelianVarietyTheory/Definitions/GlobalTwisting/SetUnipotentTranslate.lean (620 lines), ns GlobalTheory.EX.OB
  - setDiv D N h :25-31 : D7 := { D with div := { D.div with Nu := fun u => {D.div.Nu u with L := N u}, h := h, HH := max 1 (sFrame .. + RR.muMax), HH_ge := le_max_right } }  (overwrites Nu lattice and h; RR untouched)
  - Lay D :83-119 structure (rrDef : DV.RRDef D field, cmp, Gy, ...); RecOK :121-133; LedOK :138-146
  - LedPart C Y :148-159: L, ta, Gy_eq, **nuDef : DV.NuDef D L (field)**, lat : LatDefs ..., err, fdef
  - nPrime L u :372-373 := span {a•y | a ∈ DV.Iu D L u, y ∈ L.NuLat u}
  - LedPart.pt :381-401: D := setDiv D (nPrime p.L) p.ht ; **nprimeDef := fun _ => rfl** :398 ; **h_eq := fun _ => rfl** :400 ; nuDef := p.nuDef ; rrDef := Y.rrDef. ht := DV.hExpl6 D p.L Y.X C.Csz :379
  => KEY: Nu u is DEFINED as (∏ p_w^{-⌊e_w sg(u,w)⌋}) • NuLat u. NprimeDef is rfl. So "slope(Nu) = slope(NuLat) + Σ 2 l_w ⌊e sg⌋" (J.mu_diff) is ideal-twist degree formula applied to a lattice twisted BY DEFINITION by the gain exponents. Real content must then sit in (a) NuDef (NuLat vs MramL index = lenMN) and (b) divisibility: twisted Nu still pairs integrally into RR dual (DivClausesR clause 1, val2), and the h (height) = hExpl6 by rfl.
  TODO: who builds LedPart (nuDef proof), setLat (ExistsLedPart.lean:187); val2 provenance; h/HBound; OneMapIntoCC; hExpl6.
- ELP = Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLedPart.lean (229 lines), ns GlobalTheory.EX.Led
  - exists_sub :74 (submodule from predicate), exists_served :91 (A with x∈A ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg), exists_atT :106 (x∈A ↔ D.nuIn u x ∈ LT.Nlam D u w)
  - exists_lat :119-185 (proved; hyps hfull, hT, hS): ∃ N ⊆ Nu.V with InLoc_w N x ↔ cmp(nuIn x) ∈ NP at gain places (VV ≠ ∅, GIdx), ↔ nuIn x ∈ LT.Nlam at T-places, LocLe 0 N MramL elsewhere, LocEq N MramL where VV = ∅. Built by GlobalTheory.EX.Glue.exists_glue over finite set S.
  - setLat L N :187-190 := { L with NuLat := N, **lenMN := fun u w => (lenLoc (plEq w) (N u) (MramL D u)).toNat / ramIdx w** }  => NuDef clause 3 (lenLoc = lenMN*ramIdx) is by definition (hlen :207-214)
  - exists_ledPart :195-227 (proved from Std C, Val, HostArith, RecOK s C cD D, LedOK s C cD ch Y a b): uses Refill.exists_refill then exists_lat with hR.full, hR.atT, hS (from LedOK). hnu : NuDef := ⟨hN3, hN4.., hlen⟩.
  => NuLat = glue of local lattices NP (gain places) and Nlam (T places) inside MramL-space. RecOK.full/atT and LedOK are hypotheses here: to chase.
- IRZ = Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean, ns Formalism.MainNotions.G
  - VV X K a b p :292-293 := if Cand D L K p ∧ Sig X K a b p ≤ x^(-eps) then goodReps X p else ∅
  - tauP :341-344 := if VV = ∅ then 0 else X.ep p + Σ_{t0∈VV} m*(⌈tv⌉₊ + Dp + 1)
  - ioP :348 ; gainP :355-358 := if (IsResidueClassZero D p ∧ hP D p = 0) ∨ X'' < p then 0 else Σ_{t0∈VV} max(gU - Pr)(max g0 0) + Σ_{t0∈reps\VV} max g0 0
  - ParametersFill :405-414 (Prop tying L.gain j w = gainP ..., L.tau w = tauP, L.io w = ioP)
  - LatInst :422-428 (data: vOf, Fl, Lv, Ch, Vram) ; LatTied :430
  - **NP X Y K u w hg :464-472** : Submodule G.O G.Fn := span{ yProd Y u w hg VV' (p^(Σ_{t0∈VVp\VV'} ⌈Sv t0⌉) • F) | VV' ⊆ VVp, F ∈ G.M } ⊓ G.M.map(p^⌈tauP⌉ • id) ⊓ Y.Vram u w hg   (G = D.gat u w hg local datum; G.M local lattice). Non-trivial local definition.
  - LatticeLengthsAtPlace :474-481 Prop: length((M ⊓ Vram)/NP) = lenMN * vUnit ; lenMN = 0 if VV=∅
- RecBridge.lean (Formalism/LocalToGlobal/Divisibility): DivisionPackageFace :601-629 structure (Type 1): Pk : IndefPkgR, eNu, eRR, NuC, hNu : HLatTie (D.div.Nu u) (NuC (wU u)) (Dc.Xc (wU u)) (eNu u), hRR : HLatTie D.div.RR Pk.core.cols.RR Pk.core.cols.XE eRR, hBk, brTied, R, Nu, inp : ∀u, DivInputs0R ..., shift : NuC (wU u) = shiftLat (Nu u) (sgRec L u), hTie : (R u).hu - meanLog κ = D.div.h u, **foTie : 2 * FoOfR Pk.core = L.Fo**, rhs : (R u).rhs ≤ L.MAIN u + ...
  - wordFacts :633-642: builds DivInputsR with val2 := ServJointF.val2AllAtRF D L _ P.brTied hcut h2 u (P.Nu u) (ServJoint.nu_into L hN u ...) — val2 is derived (proved from brTied, CutUp, adm2, NprimeDef)
  - linkDIVt_of_rowsF :657 from BridgeRowsF (pkg : DIVinN Fm → ∃ C x0, ... Nonempty (DivisionPackageFace ...)), uses Fm.h_eq, Fm.nprimeDef
- GlobalTheoremInputs.lean:77-89 LinkDIV_at: OneMapIntoCC ∧ sFrame+RR.muMax ≤ x^CH*b ∧ ZeroAbove ∧ BesselId ∧ RRFull ∧ htMap(Bk u) ≤ h u ∧ (RR.muDual + h u - L.Fo ≤ MAIN u + ...) ∧ ...
- DataArith.lean:180 OneMapIntoCC := ∀ u, (Nu u).L.map (Bk u) ≤ D.cc ; HBound :182 htMap ≤ h
- KernelPlaceMeanBound.lean:25 hExpl6 := SZbP D L C u + Σ_j kernelPlaceMeanBound - Σ_j L6lo - meanE(log kapR)

// ChatGPT_implementation_v5.mg
//
// Brute-force but mathematically cleaner prototype for the Q-case, 2-primary
// geometric part.  Main fix relative to v4:
//   * The algebraic side is computed as actual H^1(U_2, Ghat[2^infty])
//     with U_2 acting by the cyclotomic character, not as Hom(U_2,Ghat[2]).
//   * Marking choices are variables.  For a transition C_i^k=C_j the residue
//     changes by m_i+m_j, so the code searches over markings and records a
//     witnessing marking shift.
//   * We do not quotient the residue target.  Equality is checked in Q/Z,
//     represented by Z/MZ for M the 2-part of exp(G).
//
// This is intentionally enumeration-based.  It is designed to be reliable on
// the small examples used for debugging; it is not optimized for large groups.

// -----------------------------------------------------------------------------
// Small utilities
// -----------------------------------------------------------------------------

function IsTwoPower(n)
    if n le 0 then return false; end if;
    while (n mod 2) eq 0 do n div:= 2; end while;
    return n eq 1;
end function;

function TwoPart(n)
    m := 1;
    while (n mod 2) eq 0 do
        m *:= 2;
        n div:= 2;
    end while;
    return m;
end function;

function TwoPartExponentOfGroup(G)
    e := 1;
    for g in G do
        e := LCM(e, Order(g));
    end for;
    return TwoPart(e);
end function;

function UnitMulMod(a,b,N)
    r := (a*b) mod N;
    if r eq 0 then r := N; end if;
    return r;
end function;

function UnitInvMod(a,N)
    aa := a mod N;
    for b in [1..N] do
        if GCD(b,N) eq 1 and ((aa*b - 1) mod N) eq 0 then
            return b;
        end if;
    end for;
    error "UnitInvMod: input is not a unit modulo N";
end function;

function UnitOrderMod(a,N)
    if GCD(a,N) ne 1 then
        error "UnitOrderMod: input is not a unit modulo N";
    end if;
    b := a mod N;
    if b eq 0 then b := N; end if;
    c := b;
    r := 1;
    while c ne 1 do
        c := (c*b) mod N;
        r +:= 1;
    end while;
    return r;
end function;

function UnitSubgroupClosure(gens,N)
    S := { 1 };
    changed := true;
    while changed do
        changed := false;
        T := S;
        for x in S do
            for g in gens do
                y := UnitMulMod(x,g,N);
                if not (y in T) then
                    Include(~T,y);
                    changed := true;
                end if;
            end for;
        end for;
        S := T;
    end while;
    return S;
end function;

function UnitGroupGeneratorsFromList(U2,N)
    gens := [];
    S := { 1 };
    for u in U2 do
        if not (u in S) then
            Append(~gens,u);
            S := UnitSubgroupClosure(gens,N);
        end if;
        if #S eq #U2 then break; end if;
    end for;
    return gens;
end function;

function ClassSet(G,g)
    return { x^-1*g*x : x in G };
end function;

function ClassPowerSet(G,C,k)
    return { x^k : x in C };
end function;

function ClassIndex(Csets,D)
    for j in [1..#Csets] do
        if D eq Csets[j] then return j; end if;
    end for;
    return 0;
end function;

function CleanClassRepresentatives(G, Creps)
    // Remove identity and duplicate conjugacy classes.  The identity is not a
    // ramification class; silently dropping it makes tests like [g : g in G]
    // mean the complete nontrivial set.
    reps := [];
    csets := [];
    e := Identity(G);
    for g in Creps do
        if g eq e then
            continue;
        end if;
        C := ClassSet(G,g);
        duplicate := false;
        for D in csets do
            if C eq D then
                duplicate := true;
                break;
            end if;
        end for;
        if not duplicate then
            Append(~reps,g);
            Append(~csets,C);
        end if;
    end for;
    return reps, csets;
end function;

function BitOfModuleElt(v)
    return (Integers()!Eltseq(v)[1]) mod 2;
end function;

function BitSeq(v)
    return [ (Integers()!x) mod 2 : x in Eltseq(v) ];
end function;

function CohomologyGroupGenerators(H)
    gens := [];
    for i in [1..Ngens(H)] do
        h := H.i;
        if h ne Parent(h)!0 then Append(~gens,h); end if;
    end for;
    return gens;
end function;

function LinCombF2MaybeEmpty(H, basis, coeffs)
    s := H!0;
    for j in [1..#basis] do
        if ((Integers()!coeffs[j]) mod 2) eq 1 then
            s +:= basis[j];
        end if;
    end for;
    return s;
end function;

function ColumnKernel(A)
    return Nullspace(Transpose(A));
end function;

function TwoCocycleBitFunction(CM, h2elt, G)
    t := TwoCocycle(CM, h2elt);
    e := Identity(G);
    c := BitOfModuleElt(t(<e,e>));

    // Normalize by the coboundary of the 1-cochain s with s(e)=t(e,e),
    // s(g)=0 otherwise.  In characteristic 2 subtraction is addition.
    return function(g,h)
        sg := (g eq e) select c else 0;
        sh := (h eq e) select c else 0;
        sgh := (g*h eq e) select c else 0;
        return (BitOfModuleElt(t(<g,h>)) + sg + sh + sgh) mod 2;
    end function;
end function;

function SeqKey(S)
    return Sprint(S);
end function;

function VecAddMod(a,b,M)
    return [ (a[i]+b[i]) mod M : i in [1..#a] ];
end function;

function VecNegMod(a,M)
    return [ (-a[i]) mod M : i in [1..#a] ];
end function;

function VecScalarMod(c,a,M)
    return [ ((c mod M)*a[i]) mod M : i in [1..#a] ];
end function;

function VecZero(n)
    return [ 0 : i in [1..n] ];
end function;

// -----------------------------------------------------------------------------
// U_2 data
// -----------------------------------------------------------------------------

function U2Data(N)
    U := [ a : a in [1..N] | GCD(a,N) eq 1 ];
    U2 := [ a : a in U | IsTwoPower(UnitOrderMod(a,N)) ];
    Ugens := UnitGroupGeneratorsFromList(U2,N);

    RF := recformat< Modulus, U2, Generators >;
    return rec< RF | Modulus := N, U2 := U2, Generators := Ugens >;
end function;

// -----------------------------------------------------------------------------
// Input validation
// -----------------------------------------------------------------------------

function ValidateC(G, Creps, Csets)
    if #Creps eq 0 then
        return false, "No nonidentity conjugacy classes supplied.";
    end if;

    Ugens := {};
    for C in Csets do Ugens := Ugens join C; end for;
    if sub< G | [ x : x in Ugens ] > ne G then
        return false, "The union of the supplied conjugacy classes does not generate G.";
    end if;

    unitsG := [ a : a in [1..#G] | GCD(a,#G) eq 1 ];
    for i in [1..#Csets] do
        for t in unitsG do
            D := ClassPowerSet(G, Csets[i], t);
            if ClassIndex(Csets,D) eq 0 then
                return false,
                    Sprintf("The supplied classes are not closed under invertible power t=%o on class %o.", t, i);
            end if;
        end for;
    end for;

    return true, "ok";
end function;

function PowerTransitionRows(G, Csets, U2)
    rows := [];
    for i in [1..#Csets] do
        for k in U2 do
            j := ClassIndex(Csets, ClassPowerSet(G, Csets[i], k));
            if j eq 0 then
                error Sprintf("PowerTransitionRows: class %o powered by %o is not among the supplied classes.", i, k);
            end if;
            Append(~rows, <i,k,j>);
        end for;
    end for;
    return rows;
end function;

// -----------------------------------------------------------------------------
// Geometric part
// -----------------------------------------------------------------------------

function TrivialF2CohomologyModule(G)
    F := GF(2);
    mats := [ IdentityMatrix(F,1) : i in [1..Ngens(G)] ];
    M := GModule(G, mats);
    return CohomologyModule(G, M);
end function;

function GeometricResidueKernel(G, Creps, CM)
    F := GF(2);
    H2 := CohomologyGroup(CM,2);
    H2basis := CohomologyGroupGenerators(H2);
    twos := [ TwoCocycleBitFunction(CM, b, G) : b in H2basis ];

    nrows := &+[ Ngens(Centralizer(G,g)) : g in Creps ];
    A := ZeroMatrix(F, nrows, #H2basis);

    row := 0;
    for i in [1..#Creps] do
        gi := Creps[i];
        ZG := Centralizer(G, gi);
        for ell in [1..Ngens(ZG)] do
            h := ZG.ell;
            row +:= 1;
            for j in [1..#H2basis] do
                A[row,j] := F!((twos[j](gi,h) + twos[j](h,gi)) mod 2);
            end for;
        end for;
    end for;

    K := ColumnKernel(A);
    KbasisCoords := [ BitSeq(v) : v in Basis(K) ];
    KbasisH2 := [];
    for v in KbasisCoords do
        Append(~KbasisH2, LinCombF2MaybeEmpty(H2, H2basis, v));
    end for;

    RF := recformat< H2, H2Basis, ResidueMatrix, Kernel, KernelBasisCoords, KernelBasisH2 >;
    return rec< RF | H2 := H2, H2Basis := H2basis, ResidueMatrix := A,
                     Kernel := K, KernelBasisCoords := KbasisCoords,
                     KernelBasisH2 := KbasisH2 >;
end function;

function CentralExtensionFromH2(G, CM, h2elt)
    f := TwoCocycleBitFunction(CM, h2elt, G);
    Gelts := [ g : g in G ];
    idx := AssociativeArray();
    for i in [1..#Gelts] do idx[Gelts[i]] := i; end for;
    nG := #Gelts;
    eG := Identity(G);

    function PairIndex(a,g)
        return (a mod 2)*nG + idx[g];
    end function;

    function IndexPair(p)
        a := (p-1) div nG;
        i := ((p-1) mod nG) + 1;
        return a, Gelts[i];
    end function;

    S := Sym(2*nG);

    function LeftPerm(a,g)
        imgs := [];
        for p in [1..2*nG] do
            b,h := IndexPair(p);
            c := (a + b + f(g,h)) mod 2;
            Append(~imgs, PairIndex(c, g*h));
        end for;
        return S!imgs;
    end function;

    gens := [ LeftPerm(1,eG) ];
    gens cat:= [ LeftPerm(0,G.i) : i in [1..Ngens(G)] ];
    E := sub< S | gens >;
    z := E!LeftPerm(1,eG);

    function Lift(g)
        return E!LeftPerm(0,g);
    end function;

    function Projection(x)
        p0 := PairIndex(0,eG);
        q := p0^x;
        a,g := IndexPair(q);
        return g;
    end function;

    RF := recformat< E, z, Lift, Projection, CocycleBit, GElements >;
    return rec< RF | E := E, z := z, Lift := Lift, Projection := Projection,
                     CocycleBit := f, GElements := Gelts >;
end function;

function BaseGeometricResidueBits(G, Creps, ResidueIndex, Ext)
    E := Ext`E;
    z := Ext`z;
    Lift := Ext`Lift;
    vals := [];
    for row in ResidueIndex do
        i := row[1];
        k := row[2];
        j := row[3];
        lhs := Lift(Creps[i])^k;
        rhs := Lift(Creps[j]);
        if IsConjugate(E, lhs, rhs) then
            Append(~vals, 0);
        elif IsConjugate(E, lhs, z*rhs) then
            Append(~vals, 1);
        else
            error Sprintf("Geometric residue error on transition class %o --%o--> %o.", i, k, j);
        end if;
    end for;
    return vals;
end function;

function AdjustResidueByMarking(base, ResidueIndex, shifts)
    vals := [];
    for r in [1..#ResidueIndex] do
        i := ResidueIndex[r][1];
        j := ResidueIndex[r][3];
        Append(~vals, (base[r] + shifts[i] + shifts[j]) mod 2);
    end for;
    return vals;
end function;

function AllBitVectors(n)
    if n eq 0 then return [ [] ]; end if;
    return [ [ ((mask div 2^(i-1)) mod 2) : i in [1..n] ] : mask in [0..2^n-1] ];
end function;

function EnumerateGeometricMarkedResidues(G, Creps, CM, GK, ResidueIndex)
    geom := [];
    d := #GK`KernelBasisH2;
    allGeoCoords := AllBitVectors(d);
    allMarkings := AllBitVectors(#Creps);

    for coords in allGeoCoords do
        h2 := LinCombF2MaybeEmpty(GK`H2, GK`KernelBasisH2, coords);
        Ext := CentralExtensionFromH2(G, CM, h2);
        base := BaseGeometricResidueBits(G, Creps, ResidueIndex, Ext);
        for shifts in allMarkings do
            res := AdjustResidueByMarking(base, ResidueIndex, shifts);
            Append(~geom, <coords, shifts, res>);
        end for;
    end for;
    return geom;
end function;

// -----------------------------------------------------------------------------
// Algebraic side: H^1(U_2, Ghat[2^infty])
// -----------------------------------------------------------------------------

function HomCharactersToZM(G,M)
    Gelts := [ g : g in G ];
    idx := AssociativeArray();
    for i in [1..#Gelts] do idx[Gelts[i]] := i; end for;
    gens := [ G.i : i in [1..Ngens(G)] ];
    m := #gens;
    zero := [ 0 : x in Gelts ];

    if M eq 1 or m eq 0 then
        return [ zero ], Gelts, idx;
    end if;

    possible := [];
    for i in [1..m] do
        Append(~possible, [ a : a in [0..M-1] | ((Order(gens[i])*a) mod M) eq 0 ]);
    end for;

    function Extends(assign)
        e := Identity(G);
        A := AssociativeArray();
        A[e] := 0;
        for i in [1..m] do
            g := gens[i];
            v := assign[i] mod M;
            if IsDefined(A,g) and A[g] ne v then return false, zero; end if;
            A[g] := v;
        end for;

        stepGens := [];
        stepVals := [];
        for i in [1..m] do
            Append(~stepGens, gens[i]);
            Append(~stepVals, assign[i] mod M);
            Append(~stepGens, gens[i]^-1);
            Append(~stepVals, (-assign[i]) mod M);
        end for;

        queue := [ e ];
        head := 1;
        while head le #queue do
            x := queue[head];
            head +:= 1;
            vx := A[x];
            for t in [1..#stepGens] do
                y := x*stepGens[t];
                vy := (vx + stepVals[t]) mod M;
                if IsDefined(A,y) then
                    if A[y] ne vy then return false, zero; end if;
                else
                    A[y] := vy;
                    Append(~queue,y);
                end if;
            end for;
        end while;

        vals := [];
        for x in Gelts do
            if not IsDefined(A,x) then return false, zero; end if;
            Append(~vals, A[x] mod M);
        end for;
        return true, vals;
    end function;

    chars := [];
    seen := AssociativeArray();

    procedure Recurse(pos, vals, ~chars, ~seen)
        if pos gt m then
            ok, ch := Extends(vals);
            if ok then
                key := SeqKey(ch);
                if not IsDefined(seen,key) then
                    seen[key] := true;
                    Append(~chars,ch);
                end if;
            end if;
            return;
        end if;
        for a in possible[pos] do
            Recurse(pos+1, vals cat [a], ~chars, ~seen);
        end for;
    end procedure;

    Recurse(1, [], ~chars, ~seen);
    return chars, Gelts, idx;
end function;

function ExtendU2Cocycle(Udata, M, Aelts, UgenVals)
    N := Udata`Modulus;
    U2 := Udata`U2;
    Ugens := Udata`Generators;
    nA := #Aelts[1];
    zeroA := VecZero(nA);

    Fmap := AssociativeArray();
    Fmap[1] := zeroA;

    stepUnits := [];
    stepVals := [];
    for sidx in [1..#Ugens] do
        s := Ugens[sidx];
        fs := UgenVals[sidx];
        Append(~stepUnits, s);
        Append(~stepVals, fs);
        sinv := UnitInvMod(s,N);
        // f(s^-1) = s^-1*(-f(s))
        Append(~stepUnits, sinv);
        Append(~stepVals, VecScalarMod(sinv, VecNegMod(fs,M), M));
    end for;

    queue := [ 1 ];
    head := 1;
    while head le #queue do
        x := queue[head];
        head +:= 1;
        fx := Fmap[x];
        for t in [1..#stepUnits] do
            s := stepUnits[t];
            y := UnitMulMod(x,s,N);
            // f(x*s) = f(x) + x*f(s)
            fy := VecAddMod(fx, VecScalarMod(x, stepVals[t], M), M);
            if IsDefined(Fmap,y) then
                if Fmap[y] ne fy then return false, []; end if;
            else
                Fmap[y] := fy;
                Append(~queue,y);
            end if;
        end for;
    end while;

    vals := [];
    for u in U2 do
        if not IsDefined(Fmap,u) then return false, []; end if;
        Append(~vals, Fmap[u]);
    end for;
    return true, vals;
end function;

function EnumerateU2Z1(Udata, M, Aelts)
    Ugens := Udata`Generators;
    if #Ugens eq 0 then
        nA := #Aelts[1];
        return [ [ VecZero(nA) ] ];
    end if;

    Z := [];
    seen := AssociativeArray();

    procedure Recurse(pos, vals, ~Z, ~seen)
        if pos gt #Ugens then
            ok, coc := ExtendU2Cocycle(Udata, M, Aelts, vals);
            if ok then
                key := SeqKey(coc);
                if not IsDefined(seen,key) then
                    seen[key] := true;
                    Append(~Z,coc);
                end if;
            end if;
            return;
        end if;
        for a in Aelts do
            Recurse(pos+1, vals cat [a], ~Z, ~seen);
        end for;
    end procedure;

    Recurse(1, [], ~Z, ~seen);
    return Z;
end function;

function U2Coboundaries(Udata, M, Aelts)
    U2 := Udata`U2;
    B := [];
    seen := AssociativeArray();
    for a in Aelts do
        cob := [ VecScalarMod(u-1, a, M) : u in U2 ];
        key := SeqKey(cob);
        if not IsDefined(seen,key) then
            seen[key] := true;
            Append(~B,cob);
        end if;
    end for;
    return B;
end function;

function CocycleAdd(c1,c2,M)
    return [ VecAddMod(c1[i], c2[i], M) : i in [1..#c1] ];
end function;

function H1U2GhatData(G, Creps, Udata, ResidueIndex)
    M := TwoPartExponentOfGroup(G);
    Aelts, Gelts, Gidx := HomCharactersToZM(G,M);
    Z1 := EnumerateU2Z1(Udata, M, Aelts);
    B1 := U2Coboundaries(Udata, M, Aelts);

    Upos := AssociativeArray();
    for i in [1..#Udata`U2] do Upos[Udata`U2[i]] := i; end for;

    used := AssociativeArray();
    classes := [];
    for z in Z1 do
        key := SeqKey(z);
        if IsDefined(used,key) then continue; end if;
        classKeys := [];
        for b in B1 do
            zb := CocycleAdd(z,b,M);
            k := SeqKey(zb);
            used[k] := true;
            Append(~classKeys,k);
        end for;
        Append(~classes, <z, classKeys>);
    end for;

    residues := [];
    for C in classes do
        coc := C[1];
        res := [];
        for row in ResidueIndex do
            i := row[1];
            k := row[2];
            up := Upos[k];
            chi := coc[up];
            Append(~res, chi[Gidx[Creps[i]]] mod M);
        end for;
        Append(~residues, res);
    end for;

    RF := recformat< Modulus, AElements, GElements, GIndex,
                     Z1, B1, H1Classes, Residues >;
    return rec< RF | Modulus := M, AElements := Aelts, GElements := Gelts,
                     GIndex := Gidx, Z1 := Z1, B1 := B1,
                     H1Classes := classes, Residues := residues >;
end function;

// -----------------------------------------------------------------------------
// Matching
// -----------------------------------------------------------------------------

function GeomBitsToZM(bits,M)
    if M eq 1 then
        return [ 0 : b in bits ];
    end if;
    half := M div 2;
    return [ (bits[i]*half) mod M : i in [1..#bits] ];
end function;

function MatchByEnumeration(GeomMarked, AlgData)
    M := AlgData`Modulus;
    pairs := [];
    seen := AssociativeArray();

    for gr in GeomMarked do
        gcoords := gr[1];
        shifts := gr[2];
        gresZM := GeomBitsToZM(gr[3], M);
        for aidx in [1..#AlgData`H1Classes] do
            if gresZM eq AlgData`Residues[aidx] then
                key := Sprint(<gcoords,aidx>);
                if not IsDefined(seen,key) then
                    seen[key] := true;
                    Append(~pairs, <gcoords, aidx, shifts>);
                end if;
            end if;
        end for;
    end for;
    return pairs;
end function;

// -----------------------------------------------------------------------------
// Main function and helpers to recover exact sequences
// -----------------------------------------------------------------------------

function PartiallyRamifiedBrauerPairs(G, Creps : CheckInput := true)
    RF := recformat< Ok, Message, G, GOrder, Modulus, CRepresentatives, OriginalCRepresentatives,
                     Csets, U2Data, ResidueIndex, CM,
                     H2, H2Basis, GeometricResidueToH1Matrix,
                     GeometricKernelBasisCoords, GeometricBasisH2,
                     GeometricMarkedResidues,
                     AlgebraicData, AlgebraicModulus, AlgebraicClasses,
                     AlgebraicResidues, MatchingPairs, MatchingPairsEnumerated >;

    CleanCreps, Csets := CleanClassRepresentatives(G, Creps);

    if (#G mod 2) eq 1 then
        return rec< RF | Ok := true,
                         Message := "Odd order group: non-trivial 2-primary Brauer data is zero.",
                         G := G, GOrder := #G, Modulus := 2*#G,
                         OriginalCRepresentatives := Creps,
                         CRepresentatives := CleanCreps,
                         Csets := Csets,
                         MatchingPairs := [ <[],1,[]> ],
                         MatchingPairsEnumerated := true >;
    end if;

    N := 2*#G;
    Udata := U2Data(N);

    if CheckInput then
        ok, msg := ValidateC(G, CleanCreps, Csets);
        if not ok then
            return rec< RF | Ok := false, Message := msg, G := G, GOrder := #G,
                             Modulus := N, OriginalCRepresentatives := Creps,
                             CRepresentatives := CleanCreps, Csets := Csets >;
        end if;
    end if;

    ResidueIndex := PowerTransitionRows(G, Csets, Udata`U2);
    CM := TrivialF2CohomologyModule(G);
    GK := GeometricResidueKernel(G, CleanCreps, CM);
    GeomMarked := EnumerateGeometricMarkedResidues(G, CleanCreps, CM, GK, ResidueIndex);
    Alg := H1U2GhatData(G, CleanCreps, Udata, ResidueIndex);
    Pairs := MatchByEnumeration(GeomMarked, Alg);

    return rec< RF | Ok := true, Message := "ok", G := G, GOrder := #G, Modulus := N,
                     OriginalCRepresentatives := Creps,
                     CRepresentatives := CleanCreps, Csets := Csets,
                     U2Data := Udata, ResidueIndex := ResidueIndex, CM := CM,
                     H2 := GK`H2, H2Basis := GK`H2Basis,
                     GeometricResidueToH1Matrix := GK`ResidueMatrix,
                     GeometricKernelBasisCoords := GK`KernelBasisCoords,
                     GeometricBasisH2 := GK`KernelBasisH2,
                     GeometricMarkedResidues := GeomMarked,
                     AlgebraicData := Alg, AlgebraicModulus := Alg`Modulus,
                     AlgebraicClasses := Alg`H1Classes,
                     AlgebraicResidues := Alg`Residues,
                     MatchingPairs := Pairs,
                     MatchingPairsEnumerated := true >;
end function;

function H2ElementFromPair(R, P)
    return LinCombF2MaybeEmpty(R`H2, R`GeometricBasisH2, P[1]);
end function;

function GeometricExtensionOfPair(R, P)
    h2 := H2ElementFromPair(R,P);
    return CentralExtensionFromH2(R`G, R`CM, h2);
end function;

function MarkedClassesOfPair(R, P)
    Ext := GeometricExtensionOfPair(R,P);
    E := Ext`E;
    z := Ext`z;
    Lift := Ext`Lift;
    shifts := P[3];
    Dclasses := [];
    for i in [1..#R`CRepresentatives] do
        x := Lift(R`CRepresentatives[i]);
        if shifts[i] eq 1 then x := z*x; end if;
        Append(~Dclasses, ClassSet(E,x));
    end for;
    return Dclasses;
end function;

function AlgebraicCocycleOfPair(R, P)
    // Returns a representative cocycle U_2 -> Ghat[2^infty].  The values are
    // characters G -> Z/MZ stored as value-vectors on R`AlgebraicData`GElements.
    return R`AlgebraicClasses[P[2]][1];
end function;

procedure PrintBrauerPairSummary(R)
    if not R`Ok then
        printf "Input failed: %o\n", R`Message;
        return;
    end if;
    printf "Status: %o\n", R`Message;
    printf "|G| = %o, modulus 2|G| = %o\n", R`GOrder, R`Modulus;
    printf "number of nonidentity input classes = %o\n", #R`CRepresentatives;
    if assigned R`GeometricBasisH2 then
        printf "dim geometric H^2 residue kernel = %o\n", #R`GeometricBasisH2;
        printf "|H^1(U_2,Ghat[2^infty])| = %o\n", #R`AlgebraicClasses;
        printf "algebraic modulus M = %o\n", R`AlgebraicModulus;
        printf "number of residue transition coordinates = %o\n", #R`ResidueIndex;
        printf "number of marked geometric residue candidates = %o\n", #R`GeometricMarkedResidues;
        printf "number of matching pairs = %o\n", #R`MatchingPairs;
    else
        printf "trivial/early-return case; matching pairs = %o\n", R`MatchingPairs;
    end if;
end procedure;

// Example:
//   load "ChatGPT_implementation_v5.mg";
//   G := CyclicGroup(4);
//   R := PartiallyRamifiedBrauerPairs(G,[G.1,G.1^3]);
//   PrintBrauerPairSummary(R);
//   P := R`MatchingPairs[2];
//   Ext := GeometricExtensionOfPair(R,P);
//   E := Ext`E; z := Ext`z; K := sub< E | z >;

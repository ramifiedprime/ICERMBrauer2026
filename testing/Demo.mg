load "main.mg";

procedure printdata(R)
    printf "BrauerGroup: %o\nExtra factor: %o\n\n", AbelianInvariants(R`Btilde), AbelianInvariants(R`Gabmod2);
end procedure;

procedure printheader(name)
    printf "\n----------------------------------------\n" cat name cat "\n----------------------------------------\n";
end procedure;


printheader("SYMMETRIC GROUPS WITH TRANSPOSITIONS");
for n in [4..8] do
    G:=Sym(n);
    C:=[G!(1,2)];
    R:=Btilde(G,C);
    printf "S_%o\n", n;
    printdata(R);
end for;

printheader("ALTERNATING GROUPS WITH THREE-CYCLES");
for n in [4..8] do
    G:=Alt(n);
    C:=[G!(1,2,3)];
    R:=Btilde(G,C);
    printf "A_%o\n", n;
    printdata(R);
end for;

printheader("CYCLIC GROUPS WITH ALL ELEMENTS");
for k in [1..7] do
    n:=2^k;
    G:=CyclicGroup(n);
    C:=[g: g in G| g ne Id(G)];
    R:=Btilde(G,C);
    printf "C_%o\n", n;
    printdata(R);
end for;

printheader("CYCLIC GROUPS WITH INVERTIBLE ELEMENTS");
for k in [1..7] do
    n:=2^k;
    G:=CyclicGroup(n);
    C:=[G.1^k : k in [1..n] | IsOdd(k)];
    R:=Btilde(G,C);
    printf "C_%o\n", n;
    printdata(R);
end for;

printheader("BICYCLIC GROUPS WITH ALL ELEMENTS");
for k in [1..5] do
    n:=2^k;
    G:=PermutationGroup(AbelianGroup([n,n]));
    C:=[g: g in G| g ne Id(G)];
    R:=Btilde(G,C);
    printf "C_%o x C_%o\n", n, n;
    printdata(R);
end for;
// printf "\n----------------------------------------\nSPECIAL GROUP\n----------------------------------------\n";
//     G:=PermutationGroup(FPGroup(SmallGroup(32,5)));
//     g:=Random(G);
//     while Order(g) ne 8 do g:=Random(G); end while; 
//     C:=[x[3] : x in ConjugacyClasses(G) | x[1] eq 8];
//     R:=Btilde(G,C);
//     printf "%o\n", GroupName(G);
//     printdata(R);
// for GC in testgroups do
//     R:=Btilde(GC[1],GC[2]);
//     // print G;
//     // print C;
//     print GroupName(GC[1]);
//     print R`Btilde;
//     print "";
// end for;



//     G:=CyclicGroup(4);
//     C:=[ G.1, G.1^3 ];
// Append(~testgroups, [*G,C*]);
//     G:=CyclicGroup(8);
//     C:=[ g : g in G | g ne Id(G)];
// Append(~testgroups, [*G,C*]);
//     G:=Sym(4);
//     C:=[ G!(1,2), G!(1,2,3) ];
// Append(~testgroups, [*G,C*]);
//     G:=Alt(4);
//     C:=[ G!(1,2,3), G!(1,2,4) ];
// Append(~testgroups, [*G,C*]);


// // procedure testsize(G,C)
// //     R := PartiallyRamifiedBrauerPairs(G, C);
// //     printf "Group: %o\nConjugacy Classes: %o\nSize of Brauer: %o\n\n", GroupName(G), C, #R`MatchingPairs;
// // end procedure;

// for GC in testgroups do
//     R:=Btilde(GC[1],GC[2]);
//     // print G;
//     // print C;
//     print GroupName(GC[1]);
//     print R`Btilde;
//     print "";
// end for;






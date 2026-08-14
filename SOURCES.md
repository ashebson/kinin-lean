# Sources, numbering, and assumptions

## Primary texts

- Moshe Koppel, *Seder Kinnim: A Mathematical Commentary on Tractate
  Kinnim*, linked Otzar HaHochma scan, book 193063. The scan's bookmarks give
  the project's canonical **4 + 6 + 6 = 16** division.
- Mechon Mamre, `https://mechon-mamre.org/b/h/h5b.htm`, public Hebrew Mishnah
  text. Its electronic segmentation is **5 + 6 + 5 = 16**.
- Sefaria, `https://www.sefaria.org/Mishnah_Kinnim`, public Hebrew/English
  text and commentary index. Its standard segmentation is **4 + 5 + 6 = 15**.
- Philip Reiss, “A Mathematical Proof of Kinnim 3:2,” *The Torah U-Madda
  Journal* 9 (2000), pp. 58–75. Reiss explicitly credits Koppel's equivalent
  algebraic proof and supplies a public formulation of the largest-minority /
  smallest-majority theorem.

## Numbering crosswalk

The theorem names use the Koppel column.

| Koppel / theorem | Mechon Mamre | Sefaria | Topic |
|---|---:|---:|---|
| 1:1 | 1:1–1:2 | 1:1 | levels; closed pair; vow/gift |
| 1:2 | 1:3 | 1:2 | specified offering mixed with another/closed pair |
| 1:3 | 1:4 | 1:3 | closed pairs of equal/unequal owners |
| 1:4 | 1:5 | 1:4 | same/different reason and owner; Rabbi Yosi |
| 2:1 | 2:1 | 2:1 | loss, death, flight to offered birds |
| 2:2 | 2:2 | 2:2 | two equal groups and repeated flights |
| 2:3 | 2:3 | 2:3 | the 1-through-7 flight chain |
| 2:4 | 2:4 | 2:4a | closed and specified groups |
| 2:5 | 2:5 | 2:4b | sin / closed / burnt three-zone case |
| 2:6 | 2:6 | 2:5 | bird species and completion rules |
| 3:1 | 3:1a | 3:1 | unconsulted priest; equal groups |
| 3:2 | 3:1b | 3:2 | unequal groups; generalized majority |
| 3:3 | 3:2 | 3:3 | specified sin group and burnt group |
| 3:4 | 3:3 | 3:4 | closed and specified mixture |
| 3:5 | 3:4 | 3:5 | specified offering mixed with obligations |
| 3:6 | 3:5 | 3:6 | vow/replacement arithmetic and variants |

## Interpretive/modeling assumptions

1. Counts in owner-list algorithms are counts of **pairs**; results whose
   names end in `Birds` are individual-bird counts.
2. A closed obligatory pair is designated by service and must ultimately have
   one sin-offering and one burnt-offering. A specified bird cannot change its
   designation.
3. Ownership and liability labels are abstract natural numbers. The counting
   arguments depend on equality and block sizes, not biographical facts.
4. Chapter 2:3 models a traversal as unresolved exposure to adjacent group
   boundaries: endpoint groups have one exposure and interior groups two.
   `roundTripLoss` derives losses from those exposures. The reported
   alternative opinion protects the last endpoint on the third traversal and
   is represented separately by `roundTripLossProtectedLast`.
5. Chapter 3:2 follows Koppel/Reiss. The priest uses the fixed action list
   `canonicalHalfSplitActions`, chosen before the hidden world: exactly half
   the birds are burnts above and half sins below. A `PhysicalOwnershipWorld`
   contains one level entry for every individual bird of every owner and
   globally requires exactly half above. `physicalMajorityPayoff` counts valid
   birds directly from those lists and contains no subset-sum answer.
   `ownerLevelsValid_order_irrelevant` proves order invariance, and
   `OwnerBirdAssignment.valid_eq_compressed` proves that reducing each owner
   to its above count preserves validity. Deficit/excess balance then proves
   every physical world attains at least twice the complementary smallest
   majority. `assignmentFromAllocation` realizes the matching largest-subset
   worst world with individual bird levels, proving exact maximin optimality.
   Global interleaving of different owners' bird identities is omitted because
   the service semantics observes owner, level, and quota rather than temporal
   position; this is the remaining representation choice.
6. Chapter 3:6 expresses each possible shortfall as a list of atomic
   `ReplacementNeed` values (species plus offering designation). The scenario
   lists themselves are interpretive premises. `coverShortfalls_covers_of_mem`
   proves the computed inventory covers every scenario, and
   `coverShortfalls_minimal` proves any such supply covers the computed one.
   The Majority and Ben Azzai scenario sets remain separate.

This is a formal model of the cited readings, not a ruling for practice.

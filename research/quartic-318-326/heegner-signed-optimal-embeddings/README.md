# Direct signed optimal-embedding replay

At the fixed reference `m=455,d=323`, a direct sum over primitive quaternion embeddings recovers both signed genus halves at all 416 marked supersingular labels. The match requires the correct 53-residue orientation. The opposite orientation gives the same scalar residue in this example but different marked counts.

The local determinant sign is exactly the Type-I weight up to the fixed reference phase. This computes the same finite reference without regenerating its characteristic-zero CM orbit or evaluating a class polynomial. The comparison only reads the [already frozen reference table](../heegner-f53-fixed-example/README.md). It is not an asymptotic improvement or an evaluation of the production scalar.

- [Exact proof and reference comparison](signed-optimal-embedding-replay-r1/SIGNED-OPTIMAL-EMBEDDINGS-ON-THE-416-MARKED-ORDERS.md)
- [Signed independent review](INDEPENDENT-REVIEW.md)
- [Direct character and Type-I weight](NILPOTENT-SIGN-IS-TYPE-I-LOCALLY.md)
- [The fixed source of the 416 labels](../heegner-odd2544-theta/README.md)

In the proof's local discussion, the maximal split order at 2 and 3 is the CM order in the split quadratic algebra. The ambient level-48 Eichler order retains its marked level there.

Run with standard-library Python 3.10+:

```sh
bash replay.sh
```

For an isolated tree set `BOOK` and `REF` to the exact inputs named by the two sibling dossiers. Their full SHA-256 digests are verified in the replay. The huge-orbit algorithm is not run.

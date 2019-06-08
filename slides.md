% Formal verification of Scala programs with Stainless
% Romain Ruetschi, EPFL LARA
% June 14th, 2019

# About me

- Romain Ruetschi (just call me Romac)
- MSc in Computer Science from EPFL
- Been working for ~ 2 years as an engineer at LARA
- Currently the second most active contributor to Stainless
- Not an expert!

# What is Stainless?

Stainless is a verification framework for higher-order programs written in a (now fairly substantive) subset of Scala:

- Traits, abstract classes, case classes, implicit classes, methods
- Higher-order functions, lambdas
- Any, Nothing, co-/contra-variant type parameters
- Single inheritance
- Anonymous and local classes, inner functions
- Type members, type aliases
- GADTs
- `PartialFunction`s
- Set, Bag, List, Map, Array, Byte, Short, Int, Long, BigInt
- Local state, `while`, traits/classes with `var`s, and more...

---

Some Dotty-specific features:

- Interesection and union types
- Dependent function types
- Extension methods
- Opaque types

# What Stainless verifies

Stainless supports verifying:

- **Assertions** which should hold at the place where they are stated, but are checked statically
- **Postconditions** using `ensuring` function: assertions for return values of functions
- **Preconditions** using `require` function: assertions on function parameters
- **Loop invariants**: inductive assertions that hold in each loop iteration after the while condition check passes
- **ADT/Class invariants**: assertions on immutable parameters of constructors (which remain true for all constructed values)

---

Stainless also automatically performs **automatic checks for the absence of runtime failures**:

- completeness of pattern matching
- division by zero, array bounds checks
- map domain checks

---

Moreover, Stainless prevents *PureScala* programs from:

- creating null values or unininitalized local variables or fields
- explicitly throwing an exception
- overflows and underflows on sized integer types

# Verifying typeclasses

```scala
Seq(1, 2, 3, 4).par.fold(10)(_ - _)

// ((((10 - 1) - 2) - 3) - 4) => 0
// (10 - 1) - (2 - (3 - 4))   => 6
```

---

```scala
Seq(1, 2, 3, 4).par.fold(0)(_ + _)

// ((((10 + 1) + 2) + 3) + 4) => 10
// (10 + 1) + (2 + (3 + 4))   => 10
```

---

```scala
abstract class Semigroup[A] {
  def combine(x: A, y: A): A
  
  @law def law_assoc(x: A, y: A, z: A) =
    combine(x, combine(y, z)) == combine(combine(x, y), z)
}
```

---

```scala
abstract class Monoid[A]
  extends Semigroup[A] {

  def empty: A

  @law def law_identity(x: A) =
    combine(empty, x) == x

  @law def law_rightIdentity(x: A) =
    combine(x, empty) == x
}
```

---

```scala
case class Sum(get: BigInt)

implicit def sumMonoid = new Monoid[Sum] {
  def empty = 0
  def combine(x: Sum, y: Sum) = Sum(x.get + y.get)
}
```

---

```scala
implicit def optionMonoid[A](implicit val S: Semigroup[A]) =
  new Monoid[Option[A]] {
    def empty: Option[A] = None()

    def combine(x: Option[A], y: Option[A]) =
      x match {
        case None()   => y
        case Some(xv) => y match {
          case None()   => x
          case Some(yv) => Some(S.combine(xv, yv))
        }
      }
  }
```

---

```scala
def lemma_optionCombineAssoc(x: Option[A], y: Option[A], z: Option[A]) = {
  // TODO
}
```

---

```scala
implicit def optionMonoid[A](implicit val S: Semigroup[A]) =
  new Monoid[Option[A]] {
    // ...
    
    override def law_assoc(x: Option[A], y: Option[A], z: Option[A]) =
      super.law_assoc(x, y, z) because lemma_optionCombineAssoc(x, y, z)
  }  
```

---

```scala
implicit def optionMonoid[A](implicit val S: Semigroup[A]) =
  new Monoid[Option[A]] {
    // ...
    
    override def law_assoc(@induct x: Option[A], y: Option[A], z: Option[A]) =
      super.law_assoc(x, y, z)
  }
```

--- 

```scala
def foldMap[M, A](xs: List[A])(f: A => M)(implicit M: Monoid[A]): M =
  xs.map(f).fold(M.empty)(M.append)
  
@extern
def parFoldMap[M, A](xs: List[A])(f: A => M)(implicit M: Monoid[A]): M = {
  xs.toScala.par.map(f).fold(M.empty)(M.append)
} ensuring { res =>
  res == foldMap(xs, f)
}
```

# Termination checking

A *verified* function in stainless is guaranteed to never crash, however, it can still lead to an infinite evaluation. Stainless therefore provides a termination checker that complements the verification of safety properties.

# Under the hood

# Case studies

## ConcRope

## Parellel Map-Reduce pipeline

## Actor systems

```scala
case class Primary(backup: ActorRef, counter: Counter) extends Behavior {
require(backup.name == "backup")

def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior = msg match {
  case Inc =>
    backup ! Inc
    PrimBehav(backup, counter.increment)

  case _ => this
}
}
```

---

```scala
case class Backup(counter: Counter) extends Behavior {
  def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior = msg match {
    case Inc => BackBehav(counter.increment)
    case _ => this
  }
}
```

---

```scala
def invariant(s: ActorSystem): Boolean =
  (s.behaviors(PrimaryRef), s.behaviors(BackupRef)) match {
    case (Primary(bRef, p), Backup(b)) if bRef == BackupRef =>
      val pending = s.inboxes(PrimaryRef -> BackupRef).length
      p.value == b.value + pending
    case _ => false
  }
```

## Smart contracts verification

We also maintain a fork of Stainless, called *Smart* which supports:

- Writing smart contracts in Scala
- Specifying and proving properties of such programs, including precise reasoning about the `Uint256` data type
- Generating Solidity source code from Scala, which can then be compiled and deployed using the usual tools for the Ethereum software ecosystem

For example, we have modeled and verified a voting smart contract developed by SwissBorg.

[0] https://github.com/epfl-lara/smart

# Bonus: Refinement and dependent function types

## Refinement types

```scala
type Nat = { n: BigInt => n >= BigInt(0) }
```

---

```scala
def sortedInsert(
  xs: { List[Int] => xs.nonEmpty },
  x:  { Int => x <= xs.head }
): { res: List[Int] => isSorted(res) } = {
  x :: xs // VALID
}
```

## Dependent function types

```scala
trait Entry {
  type Key
  val key: Key
}

def extractKey(e: Entry): e.Key = e.key

def extractor: (e: Entry) => e.Key = extractKey(_)
```

---

```scala
case class IntEntry() extends Entry {
  type Key = Int
  val key: Int = 42
}

assert(extractor(entry) == 42) // VALID
```

# Other features

- sbt plugin
- metals integration
- Ghost context
- Partial evaluation

# Coming up

- VC generator via bidirectional typechecker for *System FR* (TODO: ref)
- Indexed recursive types
- Higher-kinded types
- Better support for GADTs
- WebAssembly backend
- Actually working compiler and sbt plugin 
- Better metals/IDE integration

# Further work

- Reasoning about I/O and concurrency (via ZIO?)
- Support for exceptions
- Scala 2.13 / latest Dotty / TASTY support
- Standalone front-end for a custom input language
- Eta / Frege front-end
- GraalVM/Truffle back-end

# Getting started

TODO

# Acknowledgments

TODO

# References {.allowframebreaks}

TODO

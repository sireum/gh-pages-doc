// #Sireum #Logika
import org.sireum._

val empty: ISZ[Z] = ISZ()

val seq1: ISZ[Z] = ISZ(1)

val seq2: ISZ[Z] = ISZ(2)

val seq12: ISZ[Z] = ISZ(1, 2)

val seq21: ISZ[Z] = ISZ(2, 1)

val seq23: ISZ[Z] = ISZ(2, 3)

val seq123: ISZ[Z] = ISZ(1, 2, 3)

val seq34: ISZ[Z] = ISZ(3, 4)

val seq1234: ISZ[Z] = ISZ(1, 2, 3, 4)

assert(empty.isEmpty) // empty / non empty

assert(!seq1.isEmpty) // ...

assert(seq1.nonEmpty) // ...

assert(empty.size == 0) // size

assert(seq1.size == 1) // size

assert(seq12.size == 2) // size

assert(empty :+ 1 == seq1) // append

assert(seq2 :+ 1 == seq21) // append

assert(1 +: seq2 == seq12) // prepend

assert(seq12 ++ seq34 == seq1234)

assert(seq12(0 ~> seq12(1), 1 ~> seq12(0)) == seq21) // simultaneoud update, here: "swap"

def rev[E](s: ISZ[E]): ISZ[E] = {
  var k: Z = 0
  var res = ISZ[E]()
  while (k < s.size) {
    res = s(k) +: res
    k = k + 1
  }
  return res
}

// Using interprocedural check:
//assert(rev(seq12) == seq21)

// With quantification:

def rev_contract[E](s: ISZ[E]): ISZ[E] = {
  Contract(
    Ensures(Res.size == s.size & All(0 until s.size)(i => Res(i) == s(s.size - i - 1)))
  )
  var k: Z = 0
  var res = ISZ[E]()
  while (k < s.size) {
    Invariant(
      Modifies(k, res),
      k >= 0,
      k <= s.size,
      res.size == k,
      All(0 until k)(i => res(i) == s(k - i - 1))
    )
    res = s(k) +: res
    Deduce(|- (res(0) == s(k)))
    Deduce(|- (All(1 until k+1)(i => res(i) == s(k - i))))
    Deduce(|- (All(0 until k+1)(i => res(i) == s(k - i))))
    k = k + 1
  }
  return res
}

assert(rev_contract(seq12) == seq21)
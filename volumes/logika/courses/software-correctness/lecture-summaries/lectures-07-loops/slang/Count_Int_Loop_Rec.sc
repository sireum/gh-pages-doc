// #Sireum #Logika
import org.sireum._

var p: Z = randomInt()
assume(p >= 0)

while (p > 0) {
  p = p - 1
  assert(true)
}
assert(p == 0)

var n: Z = randomInt()
assume(n >= 0)

Deduce(|- (n >= 0))        // invariant deduced at the beginning of the while-loop
while (n > 0) {
  Invariant(
    Modifies(n),
    n >= 0
  )
                           // The invariant is assumed to be true here
  Deduce(|- (n > 0))       // new fact from condition of while-loop
  Deduce(|- (n - 1 >= 0))  // proof by algebra
  n = n - 1
  Deduce(|- (n >= 0))      // invariant deduced at the end of the while-loop
}
Deduce(|- (n <= 0))        // new fact from negated condition (and algebra)
Deduce(|- (n >= 0))        // invariant directly after the while-loop
assert(n == 0)

@pure def while0(k: Z): Z = {
  Contract(
    Requires(k >= 0),
    Ensures(Res == 0)
  )
  var m: Z = k
  while (m > 0) {
    Invariant(
      Modifies(m),
      m >= 0
    )
    m = m - 1
  }
  Deduce(|- (m >= 0)) // invariant
  Deduce(|- (m <= 0)) // negation of loop condition
  return m
}

@pure def count0(k: Z): Z = {
  Contract(
    Requires(k >= 0),
    Ensures(Res == 0)
  )
  if (k == 0) {
    return k
  } else {
    return count0(k - 1)
  }
}

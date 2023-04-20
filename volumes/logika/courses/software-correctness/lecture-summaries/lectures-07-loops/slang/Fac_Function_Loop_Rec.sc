// #Sireum #Logika
import org.sireum._

// Definition by cases, equational
// Specification of the factorial function

@strictpure def fac_rec_spec(n: Z): Z = n match {
  case 0 => 1
  case m => m * fac_rec_spec(m - 1)
}

// Induction rules

// Base case
@pure def fac_rec_spec_0() {
  Contract(
    Ensures(fac_rec_spec(0) == 1)
  )
}

// Inductive case
@pure def fac_rec_spec_step(n: Z) {
  Contract(
    Requires(n > 0),
    Ensures(fac_rec_spec(n) == n * fac_rec_spec(n - 1))
  )
  Deduce(|- (n != 0))
}

// Implementation using recursion

@pure def fac_rec(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res == fac_rec_spec(n))
  )
  if (n == 0) {
    return 1
  } else {
    return n * fac_rec(n - 1)
  }
}

// Implementation using while loop

@pure def fac_it(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res == fac_rec(n))
  )
  var x: Z = 1
  var m: Z = 0;
  while (m < n) {
    Invariant(
      Modifies(x, m),
      (x == fac_rec(m)),
      (m <= n),
      (m >= 0)
    )
    Deduce(|- (m < n))
    Deduce(|- (m >= 0))
    Deduce(|- (x == fac_rec(m)))
    Deduce(|- (x * (m + 1) == fac_rec(m + 1)))
    m = m + 1
    Deduce(|- (x * m == fac_rec(m)))
    x = x * m
    Deduce(|- (x == fac_rec(m)))
  }
  Deduce(|- (m >= n))
  Deduce(|- (m <= n))
  return x
}

@pure def facimp(n: Z) {
  Contract(
    Requires(n >= 0),
    Ensures(fac_it(n) == fac_rec(n))
  )
}

// Exercise: Prove termination of both factorial function implementations

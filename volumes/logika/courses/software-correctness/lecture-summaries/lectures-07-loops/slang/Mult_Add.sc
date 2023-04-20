// #Sireum #Logika
import org.sireum._

// Inductive definition of multiplication

@strictpure def mult_spec(m: Z, n: Z): Z = m match {
  case 0 => 0
  case k => mult_spec(k - 1, n) + n
}

// Induction rules

@pure def mult_spec_0(n: Z) {
  Contract(
    Ensures(mult_spec(0, n) == 0)
  )
}

@pure def mult_spec_step(m: Z, n: Z) {
  Contract(
    Requires(m > 0),
    Ensures(mult_spec(m, n) == mult_spec(m - 1, n) + n)
  )
  Deduce(|- (m != 0))
}

@pure def mult_it(m: Z, n: Z): Z = {
  Contract(
    Requires(m >= 0),
    Ensures(Res == m * n)
  )
  var i: Z = m
  var k: Z = 0
  Deduce(|- (k == (m - i) * n))
  while (i > 0) {
    Invariant(
      Modifies(k, i),
      (i >= 0),
      (k == (m - i) * n)
    )
    Deduce(|- (k == (m - i) * n))
    Deduce(|- (k + n == (m - i) * n + n))
    Deduce(|- (k + n == (m - i + 1) * n))
    Deduce(|- (k + n == (m - (i - 1)) * n))
    k = k + n
    Deduce(|- (k == (m - (i - 1)) * n))
    i = i - 1
    Deduce(|- (k == (m - i) * n))
  }
  Deduce(|- (i <= 0))
  Deduce(|- (i == 0))
  Deduce(|- (k == (m - i) * n))
  Deduce(|- (k == (m - 0) * n))
  Deduce(|- (k == m * n))
  return k
}

// We would like to prove the following
@pure def mult_rec_mult(m: Z, n: Z): Unit = {
  Contract(
    Requires(m >= 0),
    Ensures(mult_spec(m, n) == m * n)
  )
}

// Use the structure of `mult_it` to do this
@pure def mult_mult_it(m: Z, n: Z) {
  Contract(
    Requires(m >= 0),
    Ensures(mult_spec(m, n) == m * n)
  )
  var i: Z = m
  var k: Z = 0
  while (i > 0) {
    Invariant(
      Modifies(k, i),
      (i >= 0),
      (k == (m - i) * n),
      (k == mult_spec(m - i, n))
    )
    k = k + n
    i = i - 1
  }
  Deduce(|- (k == m * n))
  Deduce(|- (k == mult_spec(m, n)))
}

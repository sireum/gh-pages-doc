// #Sireum #Logika
import org.sireum._

// Definition by cases, equational
// Specification of the fibonacci function

@strictpure def fib_rec_spec(n: Z): Z = n match {
  case 0 => 0
  case 1 => 1
  case m => fib_rec_spec(m - 1) + fib_rec_spec(m - 2)
}

// Exercise a: Specify induction rules, case 0, 1, and step
// Induction rules

@pure def fib_rec_spec_0() {
  Contract(
    Ensures(fib_rec_spec(0) == 0)
  )
}

@pure def fib_rec_spec_1() {
  Contract(
    Ensures(fib_rec_spec(1) == 1)
  )
}

@pure def fib_rec_spec_step(n: Z) {
  Contract(
    Requires(n > 1),
    Ensures(fib_rec_spec(n) == fib_rec_spec(n - 1) + fib_rec_spec(n - 2))
  )
  Deduce(|- (n != 0))
  Deduce(|- (n != 1))
}

// Exercise b: implement by recursion using condtional conditional
// Prove that `fib_rec` implements `fib_rec_spec`

@pure def fib_rec(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res == fib_rec_spec(n))
  )
  if (n == 0) {
    return 0
  } else if (n == 1) {
    return 1
  } else {
    return fib_rec(n - 1) + fib_rec(n - 2)
  }
}

// Exercise c: implement using while loop
// Prove that `fib_it` implements `fib_rec`

@pure def fib_it(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res == fib_rec(n))
  )
  if (n == 0) {
    return 0
  } else if (n == 1) {
    return 1
  } else {
    var x: Z = 0
    var y: Z = 1
    var m: Z = 1;
    while (m < n) {
      Invariant(
        Modifies(x, y, m),
        (x == fib_rec(m - 1)),
        (y == fib_rec(m)),
        (m <= n),
        (m >= 0)
      )
      Deduce(|- (m < n))
      Deduce(|- (y == fib_rec(m)))
      Deduce(|- (x + y == fib_rec(m + 1)))
      m = m + 1
      Deduce(|- (y == fib_rec(m - 1)))
      Deduce(|- (x + y == fib_rec(m)))
      Deduce(|- (y + x == fib_rec(m - 1) + fib_rec(m - 2)))
      x = 2 * y + x
      Deduce(|- (y == fib_rec(m - 1)))
      Deduce(|- (x == fib_rec(m) + fib_rec(m - 1)))
      y = x - y
      Deduce(|- (y == fib_rec(m)))
      x = x - y
      Deduce(|- (x == fib_rec(m - 1)))
    }
    Deduce(|- (m >= n))
    Deduce(|- (m == n))
    return y
  }
}

// Exercise d: Prove that `fib_it` and `fib_rec` are identical

@pure def facimp(n: Z) {
  Contract(
    Requires(n >= 0),
    Ensures(fib_it(n) == fib_rec(n))
  )
  Deduce(|-(n >= 0))
}

@pure def fib_rec_term(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res == fib_rec_spec(n))
  )
  // decreases n
  val measure_n_entry = n
  Deduce(|- (measure_n_entry >= 0))
  if (n == 0) {
    return 0
  } else if (n == 1) {
    return 1
  } else {
    val measure_n_call_1 = n - 1
    Deduce(|- (measure_n_call_1 < measure_n_entry))
    val measure_n_call_2 = n - 2
    Deduce(|- (measure_n_call_2 < measure_n_entry))
    return fib_rec_term(n - 1) + fib_rec_term(n - 2)
  }
}

@pure def fib_it_term(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res == fib_rec(n))
  )
  if (n == 0) {
    return 0
  } else if (n == 1) {
    return 1
  } else {
    var x: Z = 0
    var y: Z = 1
    var m: Z = 1;
    while (m < n) {
      // decreases n - m
      Invariant(
        Modifies(x, y, m),
        (x == fib_rec(m - 1)),
        (y == fib_rec(m)),
        (m <= n),
        (m >= 0)
      )
      val measure_n_m_pre = n - m
      Deduce(|- (measure_n_m_pre >= 0))
      m = m + 1
      x = 2 * y + x
      y = x - y
      x = x - y
      val measure_n_m_post = n - m
      Deduce(|- (measure_n_m_post < measure_n_m_pre))
    }
    return y
  }
}

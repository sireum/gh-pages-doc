// #Sireum #Logika
import org.sireum._

def sq_root_rec(n: Z, x: Z, y: Z): Z = {
  // Parameters x and y are accumulators
  Contract(
    Requires(
      n >= 0, // Precondition of sq_root
      x >= 0, // Termination
      y >= 0, // Termination
      x * x <= n, // Lower bound invariant
      n < y * y), // Upper bound invariant
    Ensures(Res[Z] * Res[Z] <= n, n < (Res[Z] + 1) * (Res[Z] + 1))
  )
  val measure_yx_entry: Z = y - x
  Deduce(|- (measure_yx_entry >= 0))
  if (x + 1 == y) {
    //
    return x
  } else {
    val z: Z = (x + y) / 2
    if (z * z <= n) {
      val measure_yx_call: Z = y - z
      Deduce(|- (measure_yx_call < measure_yx_entry))
      return sq_root_rec(n, z, y)
    } else {
      val measure_yx_call: Z = z - x
      Deduce(|-(measure_yx_call < measure_yx_entry))
      return sq_root_rec(n, x, z)
    }
  }
}

def sq_root(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res[Z] * Res[Z] <= n, n < (Res[Z] + 1) * (Res[Z] + 1))
  )
  return sq_root_rec(n, 0, n+1)
}

@pure def sq_root_rec_unfold(n: Z, x: Z, y: Z): Z = {
  if (x + 1 == y) {
    return x
  } else {
    val z: Z = (x + y) / 2
    if (z * z <= n) {
      return sq_root_rec_unfold(n, z, y)
    } else {
      return sq_root_rec_unfold(n, x, z)
    }
  }
}

@pure def sq_root_unfold(n: Z): Z = {
  return sq_root_rec_unfold(n, 0, n+1)
}

@pure def sq_root_lb(n: Z): Unit = {
  Contract(
    Requires(n >= 0),
    Ensures(sq_root_unfold(n) * sq_root_unfold(n) <= n)
  )
}

@pure def sq_root_ub(n: Z): Unit = {
  Contract(
    Requires(n >= 0),
    Ensures(n < (sq_root_unfold(n) + 1) * (sq_root_unfold(n) + 1))
  )
}

@pure def sq_root_rec_unfold_term(n: Z, x: Z, y: Z): Z = {
  val measure_yx_entry: Z = y - x
  assert(measure_yx_entry >= 0)
  if (x + 1 == y) {
    return x
  } else {
    val z: Z = (x + y) / 2
    if (z * z <= n) {
      val measure_yx_call: Z = y - z
      assert(measure_yx_call < measure_yx_entry)
      return sq_root_rec_unfold_term(n, z, y)
    } else {
      val measure_yx_call: Z = z - x
      assert(measure_yx_call < measure_yx_entry)
      return sq_root_rec_unfold_term(n, x, z)
    }
  }
}

@pure def sq_root_unfold_term(n: Z): Z = {
  return sq_root_rec_unfold_term(n, 0, n+1)
}

@pure def sq_root_lb_term(n: Z): Unit = {
  Contract(
    Requires(n >= 0),
    Ensures(sq_root_unfold_term(n) * sq_root_unfold_term(n) <= n)
  )
}

@pure def sq_root_ub_term(n: Z): Unit = {
  Contract(
    Requires(n >= 0),
    Ensures(n < (sq_root_unfold_term(n) + 1) * (sq_root_unfold_term(n) + 1))
  )
}

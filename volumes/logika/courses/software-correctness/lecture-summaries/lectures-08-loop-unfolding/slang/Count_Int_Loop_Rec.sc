// #Sireum #Logika
import org.sireum._

@pure def while0(k: Z): Z = {
  var m: Z = k
  while (m > 0) {
    m = m - 1
  }
  return m
}

@pure def while0_0(k: Z) {
  Contract(
    Requires(k >= 0),
    Ensures(while0(k) == 0)
  )
}

@pure def count0(k: Z): Z = {
  if (k == 0) {
    return k
  } else {
    return count0(k - 1)
  }
}

@pure def count0_0(k: Z) {
  Contract(
    Requires(k >= 0),
    Ensures(count0(k) == 0)
  )
}
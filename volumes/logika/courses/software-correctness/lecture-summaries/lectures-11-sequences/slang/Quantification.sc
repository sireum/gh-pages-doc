// #Sireum #Logika
import org.sireum._

assert(All(0 until 10)(i => i >= 0 & i < 10))

var x: Z = 0
while (x < 10) {
  assert(Exists(0 until 10)(i => i == x))
}

def allex_seq(s: ISZ[B]) {
  Contract(
    Requires(!s.isEmpty)
  )
  assert(!All(0 until s.size)(i => s(i)) | Exists(0 until s.size)(i => s(i)))
}
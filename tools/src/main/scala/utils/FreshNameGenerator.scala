package utils

class FreshNameGenerator {
  private val ix = new java.util.concurrent.atomic.AtomicLong()
  def fresh(prefix: String = ""): String =
    if (prefix == "") s"_${ix.getAndIncrement()}"
    else s"_${prefix}_${ix.getAndIncrement()}"
}

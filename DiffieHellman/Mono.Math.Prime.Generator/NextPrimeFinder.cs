namespace DiffieHellman.Mono.Math.Prime.Generator
{
    using System;
    using Math;

    [CLSCompliant(false)]
	internal class NextPrimeFinder : SequentialSearchPrimeGeneratorBase
	{
		protected override BigInteger GenerateSearchBase(int bits, object Context)
		{
			if (Context == null)
			{
				throw new ArgumentNullException("Context");
			}
			BigInteger bigInteger = new BigInteger((BigInteger)Context);
			bigInteger.setBit(0u);
			return bigInteger;
		}
	}
}

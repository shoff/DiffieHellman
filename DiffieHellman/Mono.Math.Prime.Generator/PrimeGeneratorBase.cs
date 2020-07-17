namespace DiffieHellman.Mono.Math.Prime.Generator
{
    using System;
    using Math;

    [CLSCompliant(false)]
	internal abstract class PrimeGeneratorBase
	{
		public virtual ConfidenceFactor Confidence => ConfidenceFactor.Medium;

		public virtual PrimalityTest PrimalityTest => PrimalityTests.SmallPrimeSppTest;

		public virtual int TrialDivisionBounds => 4000;

		protected bool PostTrialDivisionTests(BigInteger bi)
		{
			return this.PrimalityTest(bi, this.Confidence);
		}

		public abstract BigInteger GenerateNewPrime(int bits);
	}
}

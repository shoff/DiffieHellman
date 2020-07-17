namespace DiffieHellman.Tests.Mono.Math
{
    using System;
    using BigInteger = DiffieHellman.Mono.Math.BigInteger;
    using Xunit;

    public class BigIntegerTests
    {
        [Fact]
        public void Int32_Greater_Than_Zero_Is_Implicitly_Cast_To_BigInteger()
        {
            int actual = 12345;
            BigInteger actualBigInteger = actual;
            Assert.Equal(12345, actualBigInteger);
        }

        [Fact]
        public void Int32_Less_Than_Zero_Throws()
        {
            int actual = -12354;
            Assert.Throws<ArgumentOutOfRangeException>(() => CastHelper(actual));
        }


        private void CastHelper(BigInteger bigInteger)
        {
        }

    }
}
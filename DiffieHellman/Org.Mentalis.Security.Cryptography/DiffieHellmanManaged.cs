namespace DiffieHellman.Org.Mentalis.Security.Cryptography
{
    using System;
    using System.Security.Cryptography;
    using global::DiffieHellman.Mono.Math;

    public sealed class DiffieHellmanManaged : DiffieHellman
	{
		private BigInteger m_P;

		private BigInteger m_G;

		private BigInteger m_X;

		private bool m_Disposed;

		private byte[] m_OAKLEY768 = new byte[96]
		{
			255,
			255,
			255,
			255,
			255,
			255,
			255,
			255,
			201,
			15,
			218,
			162,
			33,
			104,
			194,
			52,
			196,
			198,
			98,
			139,
			128,
			220,
			28,
			209,
			41,
			2,
			78,
			8,
			138,
			103,
			204,
			116,
			2,
			11,
			190,
			166,
			59,
			19,
			155,
			34,
			81,
			74,
			8,
			121,
			142,
			52,
			4,
			221,
			239,
			149,
			25,
			179,
			205,
			58,
			67,
			27,
			48,
			43,
			10,
			109,
			242,
			95,
			20,
			55,
			79,
			225,
			53,
			109,
			109,
			81,
			194,
			69,
			228,
			133,
			181,
			118,
			98,
			94,
			126,
			198,
			244,
			76,
			66,
			233,
			166,
			58,
			54,
			32,
			255,
			255,
			255,
			255,
			255,
			255,
			255,
			255
		};

		private byte[] m_OAKLEY1024 = new byte[128]
		{
			255,
			255,
			255,
			255,
			255,
			255,
			255,
			255,
			201,
			15,
			218,
			162,
			33,
			104,
			194,
			52,
			196,
			198,
			98,
			139,
			128,
			220,
			28,
			209,
			41,
			2,
			78,
			8,
			138,
			103,
			204,
			116,
			2,
			11,
			190,
			166,
			59,
			19,
			155,
			34,
			81,
			74,
			8,
			121,
			142,
			52,
			4,
			221,
			239,
			149,
			25,
			179,
			205,
			58,
			67,
			27,
			48,
			43,
			10,
			109,
			242,
			95,
			20,
			55,
			79,
			225,
			53,
			109,
			109,
			81,
			194,
			69,
			228,
			133,
			181,
			118,
			98,
			94,
			126,
			198,
			244,
			76,
			66,
			233,
			166,
			55,
			237,
			107,
			11,
			255,
			92,
			182,
			244,
			6,
			183,
			237,
			238,
			56,
			107,
			251,
			90,
			137,
			159,
			165,
			174,
			159,
			36,
			17,
			124,
			75,
			31,
			230,
			73,
			40,
			102,
			81,
			236,
			230,
			83,
			129,
			255,
			255,
			255,
			255,
			255,
			255,
			255,
			255
		};

		private byte[] m_OAKLEY1536 = new byte[192]
		{
			255,
			255,
			255,
			255,
			255,
			255,
			255,
			255,
			201,
			15,
			218,
			162,
			33,
			104,
			194,
			52,
			196,
			198,
			98,
			139,
			128,
			220,
			28,
			209,
			41,
			2,
			78,
			8,
			138,
			103,
			204,
			116,
			2,
			11,
			190,
			166,
			59,
			19,
			155,
			34,
			81,
			74,
			8,
			121,
			142,
			52,
			4,
			221,
			239,
			149,
			25,
			179,
			205,
			58,
			67,
			27,
			48,
			43,
			10,
			109,
			242,
			95,
			20,
			55,
			79,
			225,
			53,
			109,
			109,
			81,
			194,
			69,
			228,
			133,
			181,
			118,
			98,
			94,
			126,
			198,
			244,
			76,
			66,
			233,
			166,
			55,
			237,
			107,
			11,
			255,
			92,
			182,
			244,
			6,
			183,
			237,
			238,
			56,
			107,
			251,
			90,
			137,
			159,
			165,
			174,
			159,
			36,
			17,
			124,
			75,
			31,
			230,
			73,
			40,
			102,
			81,
			236,
			228,
			91,
			61,
			194,
			0,
			124,
			184,
			161,
			99,
			191,
			5,
			152,
			218,
			72,
			54,
			28,
			85,
			211,
			154,
			105,
			22,
			63,
			168,
			253,
			36,
			207,
			95,
			131,
			101,
			93,
			35,
			220,
			163,
			173,
			150,
			28,
			98,
			243,
			86,
			32,
			133,
			82,
			187,
			158,
			213,
			41,
			7,
			112,
			150,
			150,
			109,
			103,
			12,
			53,
			78,
			74,
			188,
			152,
			4,
			241,
			116,
			108,
			8,
			202,
			35,
			115,
			39,
			255,
			255,
			255,
			255,
			255,
			255,
			255,
			255
		};

		public override string KeyExchangeAlgorithm => "1.2.840.113549.1.3";

		public override string SignatureAlgorithm => null;

		public DiffieHellmanManaged()
			: this(1024, 160, DHKeyGeneration.Static)
		{
		}

		public DiffieHellmanManaged(int bitlen, int l, DHKeyGeneration keygen)
		{
			if (bitlen < 256 || l < 0)
			{
				throw new ArgumentException();
			}
			GenerateKey(bitlen, keygen, out BigInteger p, out BigInteger g);
			Initialize(p, g, null, l, checkInput: false);
		}

		public DiffieHellmanManaged(byte[] p, byte[] g, byte[] x)
		{
			if (p == null || g == null)
			{
				throw new ArgumentNullException();
			}
			if (x == null)
			{
				Initialize(new BigInteger(p), new BigInteger(g), null, 0, checkInput: true);
			}
			else
			{
				Initialize(new BigInteger(p), new BigInteger(g), new BigInteger(x), 0, checkInput: true);
			}
		}

		public DiffieHellmanManaged(byte[] p, byte[] g, int l)
		{
			if (p == null || g == null)
			{
				throw new ArgumentNullException();
			}
			if (l < 0)
			{
				throw new ArgumentException();
			}
			Initialize(new BigInteger(p), new BigInteger(g), null, l, checkInput: true);
		}

		private void Initialize(BigInteger p, BigInteger g, BigInteger x, int secretLen, bool checkInput)
		{
			if (!p.isProbablePrime() || g <= 0 || g >= p || (x != null && (x <= 0 || x > p - 2)))
			{
				throw new CryptographicException();
			}
			if (secretLen == 0)
			{
				secretLen = p.bitCount();
			}
			this.m_P = p;
			this.m_G = g;
			if (x == null)
			{
				BigInteger bi = this.m_P - 1;
				this.m_X = BigInteger.genRandom(secretLen);
				while (this.m_X >= bi || this.m_X == 0u)
				{
					this.m_X = BigInteger.genRandom(secretLen);
				}
			}
			else
			{
				this.m_X = x;
			}
		}

		public override byte[] CreateKeyExchange()
		{
			BigInteger bigInteger = this.m_G.modPow(this.m_X, this.m_P);
			byte[] bytes = bigInteger.getBytes();
			bigInteger.Clear();
			return bytes;
		}

		public override byte[] DecryptKeyExchange(byte[] keyEx)
		{
			BigInteger bigInteger = new BigInteger(keyEx);
			BigInteger bigInteger2 = bigInteger.modPow(this.m_X, this.m_P);
			byte[] bytes = bigInteger2.getBytes();
			bigInteger2.Clear();
			return bytes;
		}

		protected override void Dispose(bool disposing)
		{
			if (!this.m_Disposed)
			{
				this.m_P.Clear();
				this.m_G.Clear();
				this.m_X.Clear();
			}
			this.m_Disposed = true;
		}

		public override DHParameters ExportParameters(bool includePrivateParameters)
		{
			DHParameters result = default(DHParameters);
			result.P = this.m_P.getBytes();
			result.G = this.m_G.getBytes();
			if (includePrivateParameters)
			{
				result.X = this.m_X.getBytes();
			}
			return result;
		}

		public override void ImportParameters(DHParameters parameters)
		{
			if (parameters.P == null)
			{
				throw new CryptographicException("Missing P value.");
			}
			if (parameters.G == null)
			{
				throw new CryptographicException("Missing G value.");
			}
			BigInteger p = new BigInteger(parameters.P);
			BigInteger g = new BigInteger(parameters.G);
			BigInteger x = null;
			if (parameters.X != null)
			{
				x = new BigInteger(parameters.X);
			}
			Initialize(p, g, x, 0, checkInput: true);
		}

		~DiffieHellmanManaged()
		{
			Dispose(disposing: false);
		}

		private void GenerateKey(int bitlen, DHKeyGeneration keygen, out BigInteger p, out BigInteger g)
		{
			if (keygen == DHKeyGeneration.Static)
			{
				switch (bitlen)
				{
				case 768:
					p = new BigInteger(this.m_OAKLEY768);
					break;
				case 1024:
					p = new BigInteger(this.m_OAKLEY1024);
					break;
				case 1536:
					p = new BigInteger(this.m_OAKLEY1536);
					break;
				default:
					throw new ArgumentException("Invalid bit size.");
				}
				g = new BigInteger(22u);
			}
			else
			{
				p = BigInteger.genPseudoPrime(bitlen);
				g = new BigInteger(3u);
			}
		}
	}
}

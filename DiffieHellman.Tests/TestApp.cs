using Org.Mentalis.Security.Cryptography;
using System;

internal class TestApp
{
	public static void Main(string[] args)
	{
		DiffieHellman diffieHellman = new DiffieHellmanManaged();
		DHParameters dHParameters = diffieHellman.ExportParameters(includePrivate: false);
		DiffieHellman diffieHellman2 = new DiffieHellmanManaged(dHParameters.P, dHParameters.G, 160);
		byte[] keyEx = diffieHellman.CreateKeyExchange();
		byte[] keyEx2 = diffieHellman2.CreateKeyExchange();
		byte[] bytes = diffieHellman.DecryptKeyExchange(keyEx2);
		byte[] bytes2 = diffieHellman2.DecryptKeyExchange(keyEx);
		Console.WriteLine("Computed secret of instance 1:");
		PrintBytes(bytes);
		Console.WriteLine("\r\nComputed secret of instance 2:");
		PrintBytes(bytes2);
		Console.WriteLine("\r\nPress ENTER to continue...");
		Console.ReadLine();
	}

	private static void PrintBytes(byte[] bytes)
	{
		if (bytes != null)
		{
			for (int i = 0; i < bytes.Length; i++)
			{
				Console.Write(bytes[i].ToString("X2"));
			}
			Console.WriteLine();
		}
	}
}

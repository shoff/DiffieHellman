namespace DiffieHellman.Mono.Xml
{
    using System;
    using System.Collections;
    using System.Security;

    [CLSCompliant(false)]
	internal class SecurityParser : MiniParser, MiniParser.IHandler, MiniParser.IReader
	{
		private SecurityElement root;

		private string xmldoc;

		private int pos;

		private SecurityElement current;

		private Stack stack;

		public SecurityParser()
		{
			this.stack = new Stack();
		}

		public void LoadXml(string xml)
		{
			this.root = null;
			this.xmldoc = xml;
			this.pos = 0;
			this.stack.Clear();
			Parse(this, this);
		}

		public SecurityElement ToXml()
		{
			return this.root;
		}

		public int Read()
		{
			if (this.pos >= this.xmldoc.Length)
			{
				return -1;
			}
			return this.xmldoc[this.pos++];
		}

		public void OnStartParsing(MiniParser parser)
		{
		}

		public void OnStartElement(string name, IAttrList attrs)
		{
			SecurityElement securityElement = new SecurityElement(name);
			if (this.root == null)
			{
				this.root = securityElement;
				this.current = securityElement;
			}
			else
			{
				SecurityElement securityElement2 = (SecurityElement)this.stack.Peek();
				securityElement2.AddChild(securityElement);
			}
			this.stack.Push(securityElement);
			this.current = securityElement;
			int length = attrs.Length;
			for (int i = 0; i < length; i++)
			{
				this.current.AddAttribute(attrs.GetName(i), attrs.GetValue(i));
			}
		}

		public void OnEndElement(string name)
		{
			this.current = (SecurityElement)this.stack.Pop();
		}

		public void OnChars(string ch)
		{
			this.current.Text = ch;
		}

		public void OnEndParsing(MiniParser parser)
		{
		}
	}
}

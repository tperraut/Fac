import java.util.ArrayList;

class Pcc {

	private static int SuivantEmpty(String[] adj, ArrayList<Integer> X, String s)
	{
		for (int i : X)
		{
			if (adj[i] == s)
				return (i);
		}
		return (-1);
	}

	private static boolean noCircuit(Char[][] adj, int size)
	{
		int		val;
		String	s = "";
		ArrayList<Integer> X = new ArrayList<Integer>(size);
		ArrayList<Integer> M = new ArrayList<Integer>(size);

		for (int i = size - 1; i >= 0; i--)
		{
			X.add(i);
			s += "0";
		}
		val = SuivantEmpty(adj, X, s);
		while (val != -1)
		{
			for (int j = 0; j < size; j++)
				adj[j][val] = '0';
			M.add(val);
			X.remove(val);
			val = SuivantEmpty(X);
		}
		return (X.isEmpty());
	}
	public static void main (String[] args){
		Char[][]	adj = {
			"01110000000",
			"00001000000",
			"00001100000",
			"00000110000",
			"00000001000",
			"00000001100",
			"00000000110",
			"00000000001",
			"00000000001",
			"00000000001",
			"00000000000"};

		if (noCircuit(adj, 11));
			System.out.println("Pas de cycle");
	}
}

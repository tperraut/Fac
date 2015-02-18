
public class Main {

	public static void main(String [] args)
	{
		// Un premier exemple.
		Passager p1 = new Passager("Pierre");
		Passager p2 = new Passager("Paul");
		Autorail a1 = new Autorail(1000, 10, 5000);
		a1.ajouterTransportable(p1);
		a1.ajouterTransportable(p2);
		System.out.println(a1.getPoids());
		Conteneur c1 = new Conteneur(800,600);
		PorteConteneurs pc1 = new PorteConteneurs(1000, 1200);
		System.out.println(pc1.toString());
		pc1.ajouterTransportable(c1);
		System.out.println(pc1.toString());
		Train t1 = new Train();
		t1.ajouterElt(a1);
		t1.ajouterElt(pc1);
		System.out.println(t1.bienForme());
		System.out.println(t1.placesRestantes());
		// À vous d'en écrire d'autres !
	}
}

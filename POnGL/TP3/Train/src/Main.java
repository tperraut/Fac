
public class Main {

	public static void main(String [] args)
	{
		// Un premier exemple.
		Passager p1 = new Passager("Pierre");
		Passager p2 = new Passager("Paul");
		Locomotive l1 = new Locomotive(1000, 5000);// Une locomotive en plus
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
		t1.ajouterElt(l1);// ajout de la locomotive
		t1.ajouterElt(a1);
		t1.ajouterElt(pc1);
		System.out.println(t1.bienForme());
		System.out.println(t1.placesRestantes());
		// Autres exemples
		Passager p3 = new Passager("Bob");
		Passager p4 = new Passager("Jean");
		Passager p5 = new Passager("Claude");
		Voiture v1 = new Voiture(1000, 5, 500);
		Voiture v2 = new Voiture(950, 4, 400);
		Voiture v3 = new Voiture(1200, 7, 700);
		v1.ajouterTransportable(p3);
		v1.ajouterTransportable(p4);
		v1.ajouterTransportable(p5);
		System.out.println(v1.getPoids());
		PorteVoitures pv1 = new PorteVoitures(1200, 5000);
		System.out.println(pv1.toString());
		pv1.ajouterTransportable(v1);
		pv1.ajouterTransportable(v2);
		pv1.ajouterTransportable(v3);
		System.out.println(pv1.toString());
		t1.ajouterElt(pv1);
		//t1.ajouterElt(l1);//test en cas de locomotive mal placee
		System.out.println(t1.bienForme());
		System.out.println(t1.placesRestantes());
	}
}

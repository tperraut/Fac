-------------------------------------------------------------------------------
-- corr_maj.sql 
-- version du 8/2/2015, tourne
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- ordres tapes par le programmeur :
-- 0.

drop table sejour;
drop table client;
drop table village;

create table client(
  idc int,
  nom varchar2(10),
  age int,
  avoir int default 2000
);

create table village(
  idv int,
  ville varchar2(12),
  activite varchar2(10),
  prix int,
  capacite int
);

create table sejour(
  ids int,
  idc int,
  idv int, 
  jour int
);

-------------------------------------------------------------------------------
-- employes :
-------------------------------------------------------------------------------
-- 1.
insert into village values(10, 'NY', 'resto', 50, 200);
insert into village values(11, 'NY', 'MOMA', 60, 300);
insert into village values(12, 'Chatelaillon', 'kitesurf', 100, 20);


-------------------------------------------------------------------------------
-- 2.
select * from village;

-------------------------------------------------------------------------------
-- 3.
update village
  set capacite = capacite + 10,
      prix = prix - 10 
  where activite = 'kitesurf';

-------------------------------------------------------------------------------
-- 4.
select * from sejour ;

-------------------------------------------------------------------------------
-- 5.
-- traitement 3 :
-- exemple sur le jour 100 :
select count(*)
  from sejour
  where jour<100;
delete sejour where jour<100;

-- "modele d'ordre" :
-- traitement 3 (j) :
--   select count(*)
--     from sejour
--     where jour<j;
--     renvoie : k
--   delete sejour where jour<j;
--   return k;

-------------------------------------------------------------------------------
-- clients :
-------------------------------------------------------------------------------
-- 6.
-- traitement 1 :

-- exemple sur Rita, age 22 :
-- choix d'un identifiant, disons 1
insert into client(idc, nom, age) values(1, 'Rita', 22);

-- exemple sur Riton, age 23 :
-- choix d'un identifiant, disons 2
insert into client(idc, nom, age) values(2, 'Riton', 23);

-- modele d'ordre :
-- traitement1(n,a) :
--   choix d'un identifiant, disons i
--   insert into client(idc, nom, age) values(i, n, a);
--   return i;

-------------------------------------------------------------------------------
-- 7.
-- traitement 2 :

-- exemple sur Rita, identifiant 1, achete pour NY le jour 45 :
select idv, prix, activite
  from village
  where ville = 'NY'
    order by prix;
  -- renvoie : idv 11, prix 60, activite MOMA
update client
  set avoir = avoir - 60
  where idc = 1
    and nom = 'Rita';
-- choix d'un identifiant, disons 100
insert into sejour values(100, 1, 11, 45);

-- exemple sur Riton, identifiant 2, pour Chatelaillon le jour 365 :
select idv, prix, activite
  from village
  where ville = 'Chatelaillon'
    order by prix;
  -- renvoie : idv 12, prix 90, activite kitesurf
update client
  set avoir = avoir - 90
  where idc = 2
    and nom = 'Riton';
-- choix d'un identifiant, disons 101
insert into sejour values(101, 2, 12, 365);

-- modele d'ordre :
-- traitement 2 (i,n,v,j) :
--   select idv, prix, activite 
--     from village 
--     where ville = v
--       order by prix;
--     renvoie : iv, p, a
--   choix d'un identifiant, disons is
--   insert into sejour values (is,i,iv,j)
--   update client 
--     set avoir = avoir-p
--     where idc = i
         and nom = n;
--   return iv, is, a

-------------------------------------------------------------------------------
-- 8.
select idv, ville, activite, prix
  from village
  where idv not in (select idv
                      from sejour);

-------------------------------------------------------------------------------
-- 9.

-- exemple sur Rita, identifiant 1 :

select *
 from client
 where idc = 1
   and nom = 'Rita';

select ids, sejour.idc, idv, jour 
  from sejour, client
  where sejour.idc = client.idc
    and client.idc = 1
    and client.nom = 'Rita';

select village.idv, ville, activite, prix, capacite
  from village, sejour, client
  where sejour.idc = client.idc
    and client.idc = 1
    and client.nom = 'Rita'
    and village.idv = sejour.idv;

-- exemple sur Rita, identifiant 2 :
select *
 from client
 where idc = 2
   and nom = 'Riton';

-- modeles d'ordre :

-- consulterClient(i,n) :
-- select *
--  from client
--  where idc = i
--    and nom = n;

-- consulterSejours(i,n) :
-- select ids, sejour.idc, idv, jour
--   from sejour, client
--   where sejour.idc = client.idc
--     and client.idc = i
--     and client.nom = n;

-- consulterVillages(i,n) :
-- select village.idv, ville, activite, prix, capacite
--   from village, sejour, client
--   where sejour.idc = client.idc
--     and client.idc = i
--     and client.nom = n
--     and village.idv = sejour.idv;

-------------------------------------------------------------------------------

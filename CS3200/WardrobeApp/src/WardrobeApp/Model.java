package WardrobeApp;

import java.nio.charset.Charset;
import java.sql.CallableStatement;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Types;

//represents wardrobe model
public class Model {
  private Connection connection;
  private User login;
  private int userID;
  private int typeID;

  public Model() {
    connection = null;
    login = null;
  }

  //returns userID
  public int getUserID() {
    return this.userID;
  }

  //connect to database
  public void connect(String username, String password, String database) {
    String connectionURL = "jdbc:mysql://localhost:3306/" + database +
            "?autoReconnect=true&useSSL=false";

    Connection connect = null;

    try {
      connect = DriverManager.getConnection(connectionURL, username, password);
      if(!(connect == null)) {
        System.out.println("Successfully connected to " + database);
      }
    }
    catch (SQLException e) {
      System.out.println("Unable to connect to the database. Please Try again: \n");
    }
    this.connection = connect;

  }

  //returns connection
  public Connection getConnection() {
    return this.connection;
  }

  //returns login
  public User getLogin() {
    return this.login;
  }

  //close database
  public void close() {
    if (this.connection == null) {
      throw new IllegalStateException(
              "Cannot disconnect from database when no connection has been established. ");
    }
    try {
      connection.close();
    }
    catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //check if username already exists in DB
  public boolean checkIfUsernameExists(String username) {
    boolean exist = false;
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call CheckIfUsernameExists(?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setString(2, username);
      stmt.execute();
      int result = stmt.getInt(1);
      if(result == 1) {
        exist = true;
      }
    } catch (SQLException e) {
      e.printStackTrace();
    }
    return exist;
  }

  //logins to DB
  public void login(String username, String password) throws Exception {
    if (this.connection == null) {
      throw new IllegalStateException(
              "Cannot login to the Database when no connection has been established. ");
    }

    if (this.login != null) {
      throw new IllegalArgumentException(
              "Cannot attempt to login to different account, while already logged into one. ");
    }


    String passwordDB = "";
    int accountID = 0;

    try {
      String query = "{CALL getUserIDAndPassword(?)}";
      ResultSet rs;
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setString(1, username);
      rs = stmt.executeQuery();
      while (rs.next()) {
        accountID = rs.getInt(1);
        passwordDB = rs.getString(2);
      }
      this.userID = accountID;

    } catch (SQLException e) {
      e.getMessage();
    }

    if (passwordDB == "" || accountID == 0) {
      throw new Exception("No such account exists in database. ");
    }
    //MD5 hashes password
    String hashedPassword = MD5Hash(password);
    if (!passwordDB.equals(hashedPassword)) {
      throw new Exception("Password given does not match the password to the given Username. ");
    }

    // sets session with this account logged in
    System.out.println("Successfully logged in to " + username);
    this.login = new User(accountID, this.connection);

    //update type count
    CallableStatement stmt = this.connection.prepareCall("{? = call getTypeIndex()}");
    stmt.registerOutParameter(1, Types.INTEGER);
    stmt.execute();
    typeID = stmt.getInt(1);
  }

  //logs out
  public void logout() {
    this.login = null;
  }

  //register new account
  public void registerAccount(String FName, String LName, int age, String gender, String emailAddress, String username, String password) {

    try {
      String query = "{CALL registerAccount(?, ?, ?, ?, ?, ?, ?)}";
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setString(1, FName);
      stmt.setString(2, LName);
      stmt.setInt(3, age);
      stmt.setString(4, gender);
      stmt.setString(5, username);
      String temp = MD5Hash(password);
      stmt.setString(6, temp);
      stmt.setString(7, emailAddress);
      stmt.executeQuery();

    } catch (SQLException e) {
      System.out.println(e.getMessage());
      System.out.print("Username taken");
    }
  }

  //method to MD5 hash a string
  public String MD5Hash(String str) {
    try {
      java.security.MessageDigest md5 = java.security.MessageDigest.getInstance("MD5");
      byte[] array = md5.digest(str.getBytes(Charset.forName("UTF-8")));
      StringBuffer sb = new StringBuffer();
      for (int i = 0; i < array.length; ++i) {
        sb.append(Integer.toHexString((array[i] & 0xFF) | 0x100).substring(1, 3));
      }
      return sb.toString();
    } catch (java.security.NoSuchAlgorithmException e) {
    }
    return null;
  }

  //adds an outfit
  public void addOutfit(String description) {
    try {
      String query = "{CALL addOutfit(?, ?)}";
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, this.userID);
      stmt.setString(2, description);
      stmt.executeQuery();
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //adds a type
  public void addType(String type, String typeDescription) {
    try {
      String query = "{CALL addType(?, ?)}";
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setString(1, type);
      stmt.setString(2, typeDescription);
      stmt.executeQuery();
      typeID++;

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //get TypeID
  public int getTypeID() {
    return this.typeID;
  }

  //adds an article
  public void addArticle(int articleType, String size, String color, String brand, String material, int price, String articleDescription, String date) {
    try {
      String query = "{CALL addArticle(?, ?, ?, ?, ?, ?, ?, ?, ?)}";
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, articleType);
      stmt.setString(2, size);
      stmt.setString(3, color);
      stmt.setString(4, brand);
      stmt.setString(5, material);
      stmt.setInt(6, price);
      stmt.setInt(7, this.userID);
      stmt.setString(8, articleDescription);
      stmt.setString(9, date);
      stmt.executeQuery();
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //adds an article to an outfit
  public void addArticleToOutfit(int articleID, int outfitID) {
    try {
      Outfit outfit = new Outfit(outfitID, this.connection);
      if(!outfit.hasArticle(articleID)) {
        String query = "{CALL addArticleToOutfit(?, ?)}";
        CallableStatement stmt = this.connection.prepareCall(query);
        stmt.setInt(1, outfitID);
        stmt.setInt(2, articleID);
        stmt.executeQuery();
      }
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //removes an article from an outfit
  public void removeArticleToOutfit(int articleID, int outfitID) {
    try {
      String query = "{CALL removeArticleToOutfit(?, ?)}";
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, outfitID);
      stmt.setInt(2, articleID);
      stmt.executeQuery();
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

}

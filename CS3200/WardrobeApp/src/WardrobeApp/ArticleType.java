package WardrobeApp;

import java.sql.CallableStatement;
import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Types;

//represents an articleType
public class ArticleType {
  private int typeID;
  Connection connection;

  public ArticleType(int typeID, Connection connection) {
    this.typeID = typeID;
    this.connection = connection;
  }

  //returns typeID
  public int getTypeID() {
    return this.typeID;
  }

  //returns type
  public String getType() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getTypeFromArticleType(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.typeID);
      stmt.execute();
      result = stmt.getString(1);
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns type description
  public String getTypeDescription() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getTypeDescriptionFromArticleType(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.typeID);
      stmt.execute();
      result = stmt.getString(1);
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

}

package models;

import com.fasterxml.jackson.annotation.JsonIgnore;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.persistence.Id;
import javax.persistence.ManyToOne;
import javax.persistence.Table;

@Entity
@Table(name = "reward_discount")
public class RewardDiscount {
  @Id
  @GeneratedValue(strategy = GenerationType.IDENTITY)
  private Integer id;
  private boolean flat;
  private float discount;
  @ManyToOne
  @JsonIgnore
  private Estimate estimate;

  public RewardDiscount(boolean flat, float discount, Estimate estimate) {
    this.flat = flat;
    this.discount = discount;
    this.estimate = estimate;
  }

  public boolean isFlat() {
    return flat;
  }

  public void setFlat(boolean flat) {
    this.flat = flat;
  }

  public float getDiscount() {
    return discount;
  }

  public void setDiscount(float discount) {
    this.discount = discount;
  }

  public Estimate getEstimate() {
    return estimate;
  }

  public void setEstimate(Estimate estimate) {
    this.estimate = estimate;
  }

  public float calculateDiscount(float base) {
    if (this.flat) {
      return -this.discount;
    } else {
      return -(base * this.discount);
    }
  }
}

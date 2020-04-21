import static org.junit.jupiter.api.Assertions.assertEquals;

import models.Estimate;
import models.Frequency;
import models.RewardDiscount;
import models.SubscriptionDiscount;
import java.util.ArrayList;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class SubscriptionEstimateDiscountTest {
  private Estimate oneTimeEst;
  private Estimate weekEst;
  private Estimate monthEst;

  private SubscriptionDiscount flatDailyDisc;
  private SubscriptionDiscount flatMonthlyDisc;
  private SubscriptionDiscount percentDailyDisc;
  private SubscriptionDiscount percentMonthlyDisc;
  private RewardDiscount flatReward;
  private RewardDiscount percentageReward;

  @BeforeEach
  void beforeEach() {
    oneTimeEst = new Estimate(6004, false, Frequency.ONETIME, Frequency.ONETIME, Frequency.ONETIME, new ArrayList<>(),
        new ArrayList<>());
    weekEst = new Estimate(9002, true, Frequency.MONTHLY, Frequency.WEEKLY, Frequency.WEEKLY, new ArrayList<>(),
        new ArrayList<>());
    monthEst = new Estimate(213840, true, Frequency.YEARLY, Frequency.MONTHLY, Frequency.MONTHLY, new ArrayList<>(),
        new ArrayList<>());

    flatDailyDisc = new SubscriptionDiscount(6.0f, Frequency.DAILY, true, null);
    flatMonthlyDisc = new SubscriptionDiscount(8.0f, Frequency.MONTHLY, true, null);
    percentDailyDisc = new SubscriptionDiscount(.05f, Frequency.DAILY, false, null);
    percentMonthlyDisc = new SubscriptionDiscount(.1f, Frequency.MONTHLY, false, null);

    flatReward = new RewardDiscount(true, 1134f, null);
    percentageReward = new RewardDiscount(false, 0.5f, null);
  }

  @Test
  void testFlatDiscount() {
    ArrayList li = new ArrayList<SubscriptionDiscount>();
    li.add(flatDailyDisc);
    oneTimeEst.setDiscounts(li);
    flatDailyDisc.setEstimate(oneTimeEst);
    assertEquals(0f, oneTimeEst.getDiscount());

    weekEst.setDiscounts(li);
    flatDailyDisc.setEstimate(weekEst);
    assertEquals(0f, weekEst.getDiscount());

    monthEst.setDiscounts(li);
    flatDailyDisc.setEstimate(monthEst);
    assertEquals(0f, monthEst.getDiscount());

    li = new ArrayList<SubscriptionDiscount>();
    li.add(flatMonthlyDisc);

    oneTimeEst.setDiscounts(li);
    flatMonthlyDisc.setEstimate(oneTimeEst);
    assertEquals(0f, oneTimeEst.getDiscount());

    weekEst.setDiscounts(li);
    flatMonthlyDisc.setEstimate(weekEst);
    assertEquals(-8.0f, weekEst.getDiscount());

    monthEst.setDiscounts(li);
    flatMonthlyDisc.setEstimate(monthEst);
    assertEquals(0f, monthEst.getDiscount());
  }

  @Test
  void testPercentageDiscount() {
    ArrayList li = new ArrayList<SubscriptionDiscount>();
    li.add(percentDailyDisc);
    oneTimeEst.setDiscounts(li);
    percentDailyDisc.setEstimate(oneTimeEst);
    assertEquals(0f, oneTimeEst.getDiscount());

    weekEst.setDiscounts(li);
    percentDailyDisc.setEstimate(weekEst);
    assertEquals(0f, weekEst.getDiscount());

    monthEst.setDiscounts(li);
    percentDailyDisc.setEstimate(monthEst);
    assertEquals(0f, monthEst.getDiscount());

    li = new ArrayList<SubscriptionDiscount>();
    li.add(percentMonthlyDisc);

    oneTimeEst.setDiscounts(li);
    percentMonthlyDisc.setEstimate(oneTimeEst);
    assertEquals(0f, oneTimeEst.getDiscount());

    weekEst.setDiscounts(li);
    percentMonthlyDisc.setEstimate(weekEst);
    assertEquals(-900.2f, weekEst.getDiscount());

    monthEst.setDiscounts(li);
    percentMonthlyDisc.setEstimate(monthEst);
    assertEquals(0f, monthEst.getDiscount());
  }

  @Test
  void testFlatRewardApplication() {
    ArrayList st = new ArrayList<RewardDiscount>();
    st.add(flatReward);
    weekEst.setRewards(st);
    flatReward.setEstimate(weekEst);
    assertEquals(-1134f, weekEst.getDiscount());
    assertEquals(0f, oneTimeEst.getDiscount());
  }

  @Test
  void testPercentageRewardApplication() {
    ArrayList li = new ArrayList<RewardDiscount>();
    li.add(percentageReward);
    monthEst.setRewards(li);
    percentageReward.setEstimate(monthEst);
    assertEquals(-106920f, monthEst.getDiscount());

    weekEst.setRewards(li);
    percentageReward.setEstimate(weekEst);
    assertEquals(-4501f, weekEst.getDiscount());

    oneTimeEst.setRewards(li);
    percentageReward.setEstimate(oneTimeEst);
    assertEquals(-3002f, oneTimeEst.getDiscount());
  }

  @Test
  void testDiscountAndRewardTogether() {
    ArrayList li = new ArrayList<SubscriptionDiscount>();
    ArrayList st = new ArrayList<RewardDiscount>();
    li.add(percentMonthlyDisc);
    st.add(flatReward);
    weekEst.setDiscounts(li);
    weekEst.setRewards(st);
    percentMonthlyDisc.setEstimate(weekEst);
    flatReward.setEstimate(weekEst);
    assertEquals(-2034.2f, weekEst.getDiscount(), .001);

    li = new ArrayList<SubscriptionDiscount>();
    st = new ArrayList<RewardDiscount>();
    li.add(percentMonthlyDisc);
    st.add(percentageReward);
    weekEst.setDiscounts(li);
    weekEst.setRewards(st);
    percentMonthlyDisc.setEstimate(weekEst);
    percentageReward.setEstimate(weekEst);
    assertEquals(-5401.2f, weekEst.getDiscount(), .001);
  }
}

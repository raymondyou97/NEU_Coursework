import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.when;

import repositories.ServiceAnswerRepository;
import repositories.ServiceCategoryRepository;
import repositories.ServiceQuestionRepository;
import repositories.ServiceRepository;
import repositories.UserRepository;
import java.util.ArrayList;
import models.Service;
import models.User;
import java.util.Collections;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.context.TestConfiguration;
import org.springframework.boot.test.mock.mockito.MockBean;
import org.springframework.context.annotation.Bean;
import org.springframework.test.context.junit4.SpringRunner;
import services.ServiceCategoryService;
import services.ServiceService;

@RunWith(SpringRunner.class)
public class ServiceServiceTest {

  @TestConfiguration
  static class ServiceServiceTestContextConfiguration {

    @Bean
    public ServiceService serviceService() {
      return new ServiceService();
    }

    @Bean
    public ServiceCategoryService serviceCategoryService() {
      return new ServiceCategoryService();
    }

  }

  @Before
  public void setUp() {
    User u1 = new User(1, "don", "Don", "Brown", 21020);
    User u2 = new User(2, "mattie", "Matt", "Ice", 43023);
    User u3 = new User(3, "al", "Alfred", "Morris", 33333);
    ArrayList<User> providers = new ArrayList<>();
    providers.add(u1);
    providers.add(u2);
    providers.add(u3);
    Service s1 = new Service(4, "Driving", 0, providers, new ArrayList<>());
    u1.setServices(new ArrayList<>(Collections.singletonList(s1)));
    u2.setServices(new ArrayList<>(Collections.singletonList(s1)));
    u3.setServices(new ArrayList<>(Collections.singletonList(s1)));

    when(serviceRepository.findServicesByTitle("Driving")).thenReturn(new ArrayList<>(Collections.singletonList(s1)));
    when(userRepository.findByUsername("don")).thenReturn(u1);
    when(userRepository.findByUsername("mattie")).thenReturn(u1);
    when(userRepository.findByUsername("al")).thenReturn(u1);
  }

  @MockBean
  private ServiceRepository serviceRepository;

  @MockBean
  private ServiceCategoryRepository serviceCategoryRepository;

  @MockBean
  private UserRepository userRepository;

  @MockBean
  private ServiceQuestionRepository serviceQuestionRepository;

  @MockBean
  private ServiceAnswerRepository serviceAnswerRepository;

  @Autowired
  private ServiceService serviceService;

  @Test
  public void testSearchForProviderByService() {

    ArrayList<User> calculatedResults = new ArrayList<>(serviceService.searchForProviderByService("Driving", 10000));
    assertEquals("don", calculatedResults.get(0).getUsername());
    assertEquals("al", calculatedResults.get(1).getUsername());
    assertEquals("mattie", calculatedResults.get(2).getUsername());

    ArrayList<User> calculatedResults2 = new ArrayList<>(serviceService.searchForProviderByService("Driving", 34000));
    assertEquals("al", calculatedResults2.get(0).getUsername());
    assertEquals("mattie", calculatedResults2.get(1).getUsername());
    assertEquals("don", calculatedResults2.get(2).getUsername());
  }

}

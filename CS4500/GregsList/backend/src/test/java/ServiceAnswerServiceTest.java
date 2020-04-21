import static org.mockito.Mockito.when;
import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.delete;
import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.get;
import static org.springframework.test.web.servlet.result.MockMvcResultHandlers.print;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.jsonPath;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.status;

import models.ServiceAnswer;
import java.util.ArrayList;
import java.util.List;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.web.servlet.WebMvcTest;
import org.springframework.boot.test.mock.mockito.MockBean;
import org.springframework.test.context.junit4.SpringRunner;
import org.springframework.test.web.servlet.MockMvc;
import services.ServiceAnswerService;

@RunWith(SpringRunner.class)
@WebMvcTest(ServiceAnswerService.class)
public class ServiceAnswerServiceTest {
  @Autowired
  private MockMvc mockMvc;

  @MockBean
  private ServiceAnswerService service;

  private List<ServiceAnswer> serviceAnswers = new ArrayList<>();

  @Before
  public void setup() {
    final ServiceAnswer serviceAnswer1 = new ServiceAnswer(true, null, null, null, null, null);
    serviceAnswer1.setId(24);
    final ServiceAnswer serviceAnswer2 = new ServiceAnswer(false, 1, 3, 2, null, null);
    serviceAnswer2.setId(33);
    serviceAnswers.add(serviceAnswer1);
    serviceAnswers.add(serviceAnswer2);
  }

  @Test
  public void testFindAllServiceAnswers() throws Exception {
    when(service.findAllServiceAnswers()).thenReturn(serviceAnswers);
    this.mockMvc.perform(get("/api/serviceAnswers")).andDo(print()).andExpect(status().isOk())
        .andExpect(jsonPath("$[0].id").value(24)).andExpect(jsonPath("$[1].id").value(33));
  }

  @Test
  public void testFindServiceAnswerById() throws Exception {
    when(service.findServiceAnswerById(24)).thenReturn(serviceAnswers.get(0));
    this.mockMvc.perform(get("/api/serviceAnswers/24")).andDo(print()).andExpect(status().isOk())
        .andExpect(jsonPath("$.id").value(24));
  }

  @Test
  public void testDeleteServiceAnswer() throws Exception {
    this.mockMvc.perform(delete("/api/serviceAnswers/24")).andDo(print()).andExpect(status().isOk());
  }
}
